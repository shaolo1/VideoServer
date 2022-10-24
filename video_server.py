"""
    VideoServer provides DLNA (Digital Living Network Alliance) video streaming
    via UPnP (Universal Plug and Play).
    The UPnP discovery is done via SSDP (Simple Service Discovery Protocol).

    :copyright: 2018 by shao.lo@gmail.com
    :license: GPL3, see LICENSE for more details.
"""
__version_info__ = (0, 0, 5)
__version__ = '.'.join(map(str, __version_info__))
__service_name__ = 'VideoServer'

import abc
import argparse
import asyncio
import base64
import datetime
import itertools
import logging
import mimetypes
import os
import platform
import random
import re
import socket
import struct
import time

from enum import Enum
from functools import partial
from http import HTTPStatus
from threading import Thread
from typing import List, Optional
from urllib.parse import urljoin
from xml.etree import ElementTree

from flask import Flask, Response, request, render_template, send_from_directory

app = Flask('app', template_folder=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'templates'))  # Make sure templates can be found if not running from that location


UPNP_NS = 'urn:schemas-upnp-org:metadata-1-0/upnp/'  # Universal Plug and Play namespace
ElementTree.register_namespace('upnp', UPNP_NS)  # Browse response has ns1:class vs upnp:class wo this and is unusable!


class BaseItem(abc.ABC):
    DEFAULT_ROOT_ID = '0'  # Initial browse ObjectID will be 0 for root

    def __init__(self, object_id: str, path: str, urlbase: str, parent: Optional['BaseItem'], mime_type=''):
        self._object_id = object_id
        self._parent = parent
        self._file_path = path
        self._mime_type = mime_type
        self._urlbase = urlbase
        self._date = datetime.datetime.fromtimestamp(os.stat(self._file_path).st_mtime)
        self._cover = None
        self._captions = None

    def add_child(self, child: 'BaseItem'):
        assert False

    def get_mime_type(self):
        return self._mime_type

    def get_captions(self):
        return self._captions

    def get_children(self, start, end) -> List['BaseItem']:
        return []

    def get_child_count(self):
        return 0

    def get_id(self):
        return self._object_id

    def get_update_id(self):
        return 0  # Only containers have update_id

    def get_path(self):
        return self._file_path

    def get_name(self):
        return os.path.splitext(os.path.basename(self._file_path))[0]

    def get_parent(self):
        return self._parent

    @abc.abstractmethod
    def _element_name(self):
        return 'item'

    @abc.abstractmethod
    def _upnp_class(self):
        # See http://upnp.org/resources/documents/UPnP_AV_tutorial_July2014.pdf for object hierarchy
        return 'object'

    def to_element(self, object_id: str, browse_direct_children: bool):
        root = ElementTree.Element(self._element_name(), {'id': self._object_id})
        if self._parent is not None:
            root.attrib['parentID'] = self._parent.get_id()

        ElementTree.SubElement(root, ElementTree.QName(UPNP_NS, 'class')).text = self._upnp_class()
        dc_ns = 'http://purl.org/dc/elements/1.1/'
        ElementTree.SubElement(root, ElementTree.QName(dc_ns, 'title')).text = self.get_name()
        ElementTree.SubElement(root, ElementTree.QName(dc_ns, 'date')).text = self._date.isoformat()

        if browse_direct_children:
            if self._object_id not in [self.DEFAULT_ROOT_ID, root.attrib['parentID']]:
                root.attrib['refID'] = root.attrib['id']
                root.attrib['parentID'] = self._object_id
        else:
            if self._object_id == self.DEFAULT_ROOT_ID:
                root.find(ElementTree.QName(dc_ns, 'title')).text = 'root'
            if self._object_id != root.attrib['id']:
                root.attrib['refID'] = root.attrib['id']
                root.attrib['id'] = self._object_id
        return root

    @staticmethod
    def res_element(url, mime_type, size, extra_dlna_information='*'):
        root = ElementTree.Element('res', {'protocolInfo': f'http-get:*:{mime_type}:{extra_dlna_information}', 'size': str(size)})
        root.text = url
        return root


class VideoItem(BaseItem):
    def __init__(self, object_id: str, path: str, urlbase: str, parent: BaseItem, mime_type):
        super().__init__(object_id, path, urlbase, parent, mime_type)
        assert self._mime_type.startswith('video/')

        base, _ = os.path.splitext(self.get_path())
        cover = base + '.jpg'
        if os.path.exists(cover):
            self._cover = cover

        caption = base + '.srt'  # SubRip Text subtitles file
        if os.path.exists(caption):
            self._captions = caption

    def _element_name(self):
        return super()._element_name()

    def _upnp_class(self):
        return super()._upnp_class() + '.item.videoItem'

    @staticmethod
    def _res_path(base_url, path):
        hash_from_path = base64.b64encode(path.encode()).decode('ascii')
        return f'{base_url}?res={hash_from_path}'

    def to_element(self, object_id: str, browse_direct_children: bool):
        root = super().to_element(object_id, browse_direct_children)

        stats = os.stat(self._file_path)
        size = stats.st_size

        url = urljoin(self._urlbase, self._object_id)
        root.append(self.res_element(url, self._mime_type, size))
        if self._cover:
            mime_type, _ = mimetypes.guess_type(self._cover, strict=False)
            cover = self._res_path(url, self._cover)

            size = os.path.getsize(self._cover)
            # DLNA.ORG_PN = More specific mime_type info ...tv won't display the images without the more specific mime_type
            root.append(self.res_element(cover, mime_type, size, 'DLNA.ORG_PN=JPEG_TN'))
# TODO: add resolution="1600x1200"..use pillow to get it..to see if this helps tv render better?
# <res protocolInfo="http-get:*:image/jpeg:*" size="888322" resolution="1600x1200" colorDepth="24">http://xxx:49153/IMG.jpg</res>

        if self._captions and self._captions.endswith('.srt'):
            self._captions = self._res_path(url, self._captions)
        return root


class DirectoryItem(BaseItem):
    def __init__(self, object_id: str, path: str, urlbase: str, parent: Optional[BaseItem]):  # All items except the root should have a parent
        super().__init__(object_id, path, urlbase, parent)
        self._children = []
        self._sorted = False
        # TODO: Since not supporting updates..could always return 0?!
        self._update_id = 0  # Should be incremented on every modification

    def add_child(self, child: BaseItem):
        self._children.append(child)
        self._update_id += 1

    def get_update_id(self):
        return self._update_id  # TODO: should return system_update_id for root item?!

    def get_children(self, start, end) -> List[BaseItem]:
        return self._children[start:end]

    def get_child_count(self):
        return len(self._children)

    def _element_name(self):
        return 'container'

    def _upnp_class(self):
        return super()._upnp_class() + '.container'

    def to_element(self, object_id: str, browse_direct_children: bool):
        root = super().to_element(object_id, browse_direct_children)
        if self._children:
            root.attrib['childCount'] = str(len(self._children))
        return root


class Content:
    def __init__(self, content_dir: str, urlbase):
        assert os.path.isdir(content_dir)
        self._content_dir = content_dir
        self._urlbase = urlbase + '/'  # urljoin requires trailing slash
        self._items = {}

        self._add_items()

    def get_by_id(self, id_: str) -> BaseItem:
        if id_ == BaseItem.DEFAULT_ROOT_ID:  # Initial browse request will have default root ObjectID
            id_ = self._get_id(self._content_dir)
        return self._items.get(id_, None)

    def _add_items(self):
        def add_children(parent_: DirectoryItem):
            for child in itertools.chain(sub_dirs, files):
                child_path = os.path.join(path, child)
                self._add_item(child_path, parent_)
            parent_._children.sort(key=lambda x: x.get_name())

        for path, sub_dirs, files in os.walk(self._content_dir):
            parent = self._add_item(path, None)
            add_children(parent)

    def _get_id(self, path):
        encode_path = self._content_dir if path == self._content_dir else path.replace(self._content_dir, '')
        return base64.b64encode(encode_path.encode()).decode('ascii')

    def _add_item(self, path: str, parent: Optional[BaseItem]):
        assert os.path.exists(path)

        mime_type, _ = mimetypes.guess_type(path, strict=False)  # TODO: search for .mp4 files only..vs checking mime types
        id_ = self._get_id(path)
        if os.path.isdir(path):
            item = DirectoryItem(id_, path, self._urlbase, parent)
        elif mime_type is None:
            print(f'Unknown mime type for {path}')
            return None
        elif mime_type.startswith('video/'):
            id_ += '.mp4'  # Captions won't work wo the extension!
            item = VideoItem(id_, path, self._urlbase, parent, mime_type)
        else:
            return None
        self._items[id_] = item
        if parent:
            parent.add_child(item)
        return item


class VideoServer:
    """Implements a subset of MediaServer:1 from http://upnp.org/specs/av/UPnP-av-MediaServer-v1-Device.pdf"""
    def __init__(self, host, port, content_dir, friendly_name):
        self._unique_device_name = 'video_server'
        self._urlbase = f'http://{host}:{port}'

        self._device_type = 'urn:schemas-upnp-org:device:MediaServer:1'
        self._service_type = 'urn:schemas-upnp-org:service:ContentDirectory:1'

        self._file_store = Content(content_dir, self._urlbase)
        self._ssdp_server = SSDPServer(self)

        @app.route('/favicon.ico')
        def fav_icon():
            return '', HTTPStatus.NOT_FOUND

        @app.route('/scpd.xml')
        def scpd_xml():
            """Service Control Point Definition"""
            return render_template('scpd.xml'), {'Content-Type': 'text/xml'}

        @app.route('/ctrl', methods=['POST'])
        def control():
            return self._handle_control()

        @app.route('/desc.xml')
        def desc_xml():
            xml = render_template('desc.xml', udn=self._unique_device_name, device_type=self._device_type, service_type=self._service_type,
                                  friendly_name=friendly_name, model_name=__service_name__, version=__version__)
            return xml, {'Content-Type': 'text/xml'}

        @app.route('/<media_file>', methods=['HEAD', 'GET'])
        def media(media_file):
            res = request.args.get('res')
            if res:
                path = base64.b64decode(res.encode()).decode('ascii')
                print(f'{res=} {path=} {content_dir=}')
                # return send_file(path)  # using safer send_from_directory to prevent directory traversal attack
                return send_from_directory(content_dir, res)

            item = self._file_store.get_by_id(media_file)
            if item is None:
                return '', HTTPStatus.NOT_FOUND
            _path = item.get_path()

            if request.method == 'HEAD':
                if 'getcaptioninfo.sec' in request.headers:
                    if item.get_captions():
                        response = Response('', headers={'CaptionInfo.sec': item.get_captions()}, mimetype='text/html')
                        return response
                    response = Response('<html><p>Captions srt file not found</p></html>', HTTPStatus.NOT_FOUND, mimetype='text/html')
                    return response

            part, start, end = self.get_range(request.headers)
            mime_type = item.get_mime_type()

            def generate(chunk_size=2**16):  # Default to 64k chunks
                with open(_path, 'rb') as f:
                    f.seek(start)
                    for data in iter(partial(f.read, chunk_size), b''):
                        yield data

            stats = os.stat(_path)
            end = stats.st_size if end is None else end
            size = str(end-start)

            headers = {'Content-Length': size, 'Content-Type': mime_type, 'Accept-Ranges': 'bytes',
                       # DLNA.ORG_OP = Time range capable / Byte range capable
                       'Contentfeatures.dlna.org': 'DLNA.ORG_OP=01'  # TV will try to read entire file without this
                       }
            if part:
                headers['Content-Range'] = f'bytes {start}-{end-1}/{size}'
            response = Response(generate(), HTTPStatus.PARTIAL_CONTENT if part else HTTPStatus.OK, headers=headers, direct_passthrough=True)
            # print('outbound headers', response.headers)
            return response

        @app.route('/', defaults={'path': ''})
        @app.route('/<path:path>')
        def catch_all(path):
            print('*** catch_all', path)
            return '', HTTPStatus.NOT_FOUND

    @staticmethod
    def _browse_error(code):
        assert code in [HTTPStatus.UNAUTHORIZED, HTTPStatus.BAD_REQUEST]
        rendered = render_template('browse_error.xml', code=code, desc='Invalid Action' if code == HTTPStatus.UNAUTHORIZED else 'Invalid Args')
        return Response(rendered, HTTPStatus.INTERNAL_SERVER_ERROR, mimetype='text/xml')

    def _handle_control(self):
        """Handle a SOAP command."""
        if 'text/xml' not in request.headers['content-type']:
            return self._browse_error(HTTPStatus.UNAUTHORIZED)

        def _parse():
            try:
                tree = ElementTree.fromstring(request.data)
                body = tree.find('{http://schemas.xmlsoap.org/soap/envelope/}Body')
                method_ = list(body)[0]
                uri, method_name_ = method_.tag[1:].split('}')  # '{urn:schemas-upnp-org:service:ContentDirectory:1}Browse'
                return method_, method_name_
            except Exception as e:
                print('parse error', e)
            return None, None

        method, method_name = _parse()
        if method is None:
            return self._browse_error(HTTPStatus.UNAUTHORIZED)
        if method_name != 'Browse':
            return self._browse_error(HTTPStatus.UNAUTHORIZED)
        browse_flag = method.find('BrowseFlag')
        if browse_flag is None:
            return self._browse_error(HTTPStatus.BAD_REQUEST)

        object_id = method.find('ObjectID').text
        browse_item = self._file_store.get_by_id(object_id)
        if browse_item is None:
            return self._browse_error(HTTPStatus.BAD_REQUEST)
        browse_direct_children = browse_flag.text == 'BrowseDirectChildren'
        starting_index = int(method.find('StartingIndex').text)
        requested_count = int(method.find('RequestedCount').text)

        result, total_matches, num_returned, update_id = self._browse(browse_item, browse_direct_children, starting_index, requested_count)
        # NOTE: the result node will be escaped.  Using "|safe" will generate good looking xml, but clients will not be able to use it
        rendered = render_template('browse_result.xml', result=result, total_matches=total_matches, num_returned=num_returned, update_id=update_id)
        print(f'{object_id=} {browse_item.get_name()=} {browse_item.get_path()=} {rendered=}')
        return Response(rendered, mimetype='text/xml')

    @staticmethod
    def _browse(browse_item: BaseItem, browse_direct_children: bool, starting_index: int, requested_count: int):
        object_id = browse_item.get_id()

        # Build result using Digital Item Description Language
        results_description = ElementTree.Element('DIDL-Lite', xmlns='urn:schemas-upnp-org:metadata-1-0/DIDL-Lite/')

        if browse_direct_children:
            result = browse_item.get_children(starting_index, starting_index + requested_count)
            for item in result:
                results_description.append(item.to_element(object_id, browse_direct_children))
        else:
            results_description.append(browse_item.to_element(object_id, browse_direct_children))

        total_matches = browse_item.get_child_count() if browse_direct_children else 1
        xml = ElementTree.tostring(results_description).decode()
        return xml, total_matches, len(results_description), browse_item.get_update_id()

    @staticmethod
    def get_range(headers):
        byte_range = headers.get('Range', headers.get('range'))
        match = None if not byte_range else re.match(r'bytes=(?P<start>\d+)-(?P<end>\d+)?', byte_range)
        if not match:
            return False, 0, None
        start = match.group('start')
        end = match.group('end')
        start = int(start)
        if end is not None:
            end = int(end)
        return True, start, end

    def register_devices(self, ssdp_server):
        ssdp_server.register_local(self._unique_device_name, 'upnp:rootdevice')
        ssdp_server.register_local(self._unique_device_name, self._device_type, f'{self._urlbase}/desc.xml')
        ssdp_server.register_local(self._unique_device_name, self._service_type)

    def shutdown(self):
        print('shutdown...')
        self._ssdp_server.shutdown()


class SSDPServer(asyncio.DatagramProtocol):
    """Simple Service Discovery Protocol
    see spec - http://www.upnp.org/specs/arch/UPnP-arch-DeviceArchitecture-v1.0-20080424.pdf"""
    ADDRESS = '239.255.255.250'
    PORT = 1900
    # Concatenation of OS name, OS version, UPnP/1.0, product name, and product version ..see spec
    SERVER_ID = f'{platform.system()},{platform.release()},UPnP/1.0,{__service_name__},{__version__}'

    class Header(str, Enum):
        NT = 'nt'  # Notification Type
        NTS = 'nts'  # Notification Sub Type
        ST = 'st'  # Search Target
        USN = 'usn'  # Unique Service Name
        MX = 'mx'  # Maximum wait time
        EXT = 'ext'  # Extension acknowledge flag
        SERVER = 'server'
        CACHE_CONTROL = 'cache-control'
        LOCATION = 'location'  # Device description xml url

    class Messages(str, Enum):
        ALIVE = 'ssdp:alive'
        BYE = 'ssdp:byebye'
        ALL = 'ssdp:all'

    def __init__(self, server):
        self._server = server

        @asyncio.coroutine
        def _connect():
            info = socket.getaddrinfo(SSDPServer.ADDRESS, None)[0]
            sock = socket.socket(info[0], socket.SOCK_DGRAM)
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
            sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEPORT, 1)
            group_bin = socket.inet_pton(info[0], info[4][0])
            sock.bind(('', SSDPServer.PORT))
            if info[0] == socket.AF_INET:  # IPv4
                group = group_bin + struct.pack('=I', socket.INADDR_ANY)
                sock.setsockopt(socket.IPPROTO_IP, socket.IP_ADD_MEMBERSHIP, group)
            else:
                group = group_bin + struct.pack('@I', 0)
                sock.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_JOIN_GROUP, group)
            yield from asyncio.get_event_loop().create_datagram_endpoint(lambda: self, sock=sock)

        def _run(loop):
            asyncio.set_event_loop(loop)
            loop.run_forever()
            loop.close()

        self.io_loop = asyncio.new_event_loop()
        asyncio.run_coroutine_threadsafe(_connect(), loop=self.io_loop)
        Thread(target=_run, args=(self.io_loop,)).start()

        self._devices_local = {}
        self._transport = None

    def connection_made(self, transport):
        self._transport = transport
        self._server.register_devices(self)

    def datagram_received(self, data: bytes, host_port: tuple):
        header = data.decode().split('\r\n\r\n')[0]
        lines = header.split('\r\n')
        method, target, _ = lines[0].split()
        if target != '*':
            return
        if method == 'M-SEARCH':
            headers = {x.lower(): y for x, y in (line.replace(': ', ':', 1).split(':', 1) for line in lines[1:] if len(line) > 0)}
            self._m_search_received(headers, host_port)

    def register_local(self, unique_device_name, search_target, location=''):
        usn = f'{unique_device_name}::{search_target}'

        # TODO: from https://dangfan.me/en/posts/upnp-intro
        # Cache-control: The integer following max-age= specifies the number of seconds the advertisement is valid,
        # which indicates that the device need to resend this notification before expiration....TODO so need to resend?!
        device = {SSDPServer.Header.USN: usn, SSDPServer.Header.ST: search_target,
                  SSDPServer.Header.EXT: '',  # Required by spec...confirms message was understood
                  SSDPServer.Header.CACHE_CONTROL: 'max-age=1800',  # 1800 = 30 minutes
                  SSDPServer.Header.SERVER: SSDPServer.SERVER_ID}
        if location:
            device[SSDPServer.Header.LOCATION] = location

        self._devices_local[usn] = device
        self._send_alive(usn)

    def _send(self, message: str, destination: tuple):
        try:
            self._transport.sendto(message.encode(), destination)
        except socket.error as e:
            print('_send', e)

    def _send_discovery_response(self, response, destination):
        self._send(response, destination)

    @staticmethod
    def _make_message(parts, data):
        parts.extend([f'{k}: {v}' for k, v in data.items()])
        return '\r\n'.join(parts) + '\r\n\r\n'

    @staticmethod
    def _make_discovery_response(device):
        date = time.strftime('%a, %0d %b %Y %H:%M:%S GMT', time.gmtime())
        parts = ['HTTP/1.1 200 OK', f'date: {date}']
        return SSDPServer._make_message(parts, device)

    def _m_search_received(self, headers, host_port):
        max_delay = int(headers[SSDPServer.Header.MX])
        search_target = headers[SSDPServer.Header.ST]
        for device in self._devices_local.values():
            if device[SSDPServer.Header.ST] != search_target and search_target != SSDPServer.Messages.ALL:
                continue
            response = self._make_discovery_response(device)
            if max_delay > 5:
                print('max_delay', max_delay)  # TODO: cap at 5? per spec
            delay = random.randint(0, max_delay)  # Use random delay to prevent flooding (required by spec)
            asyncio.get_event_loop().call_later(delay, self._send_discovery_response, response, host_port)

    def _make_notify_message(self, usn, sub_type: str):
        device = self._devices_local[usn]
        data = device.copy()
        data[SSDPServer.Header.NT] = data.pop(SSDPServer.Header.ST)  # Rename ST to NT

        parts = ['NOTIFY * HTTP/1.1', f'HOST: {SSDPServer.ADDRESS}:{SSDPServer.PORT}', f'{SSDPServer.Header.NTS}: {sub_type}']
        return self._make_message(parts, data)

    def _send_alive(self, usn):
        data = self._make_notify_message(usn, SSDPServer.Messages.ALIVE)
        self._send(data, (SSDPServer.ADDRESS, SSDPServer.PORT))

    def _send_bye(self, usn):
        data = self._make_notify_message(usn, SSDPServer.Messages.BYE)
        self._send(data, (SSDPServer.ADDRESS, SSDPServer.PORT))

    def shutdown(self):
        if self._transport:
            for usn in self._devices_local:
                self._send_bye(usn)
        self.io_loop.stop()


def main():
    parser = argparse.ArgumentParser(description='Video Server')
    parser.add_argument('--host', required=True, help="Won't be accessible to other devices (computers/TVs) if localhost is used!")
    parser.add_argument('--port', default=0, type=int, help='Using 0 results in a random port.')
    parser.add_argument('--content_dir', required=True, help='The path of the video files to serve.')
    parser.add_argument('--device_name', default='Videos')
    args = parser.parse_args()

    logging.getLogger('werkzeug').setLevel(logging.ERROR)  # Disable flask request logging

    if not args.port:
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.bind((args.host, 0))  # 0 = Use random port
        args.port = sock.getsockname()[1]
        sock.close()
    server = VideoServer(args.host, args.port, args.content_dir, args.device_name)

    print(f'running at {args.host}:{args.port}')
    app.run(host=args.host, port=args.port)  # , debug=True)

    print('stopping...')
    server.shutdown()


if __name__ == '__main__':
    main()
