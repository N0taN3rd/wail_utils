from __future__ import absolute_import
import atexit
import base64
import bisect
import brotli
import calendar
import cgi
import codecs
import collections
import datetime
import hashlib
import heapq
import hmac
import itertools
import json
import logging
import mimetypes
import os
import pkg_resources
import pkgutil
import pprint
import re
import requests
import shutil
import six
import six.moves.urllib.parse as urlparse
import six.moves.html_parser
import socket
import ssl
import surt
import sys
import time
import webencodings
import yaml
import zlib
import multiprocessing
from heapq import merge
from argparse import ArgumentParser, RawTextHelpFormatter
from bisect import insort
from collections import deque
from copy import copy
from datetime import datetime, timedelta
from distutils.util import strtobool
from email.utils import parsedate, formatdate
from io import open, BytesIO
from itertools import chain
from jinja2 import Environment
from jinja2 import FileSystemLoader, PackageLoader, ChoiceLoader
from pkg_resources import resource_string
from pprint import pformat
from redis import StrictRedis
from requests import request as live_request
from shutil import rmtree
from six import iteritems
from six import StringIO
from six import text_type
from six.moves.html_parser import HTMLParser
from six.moves.http_cookies import SimpleCookie, CookieError
from six.moves import zip, range, map
from six.moves.urllib.error import HTTPError
from six.moves.urllib.parse import parse_qs,  quote
from six.moves.urllib.parse import quote_plus, unquote_plus
from six.moves.urllib.parse import urlencode
from six.moves.urllib.parse import urljoin, urlsplit, urlunsplit
from six.moves.urllib.request import pathname2url, url2pathname
from six.moves.urllib.request import urlopen, Request
from tempfile import NamedTemporaryFile, mkdtemp
from tempfile import SpooledTemporaryFile
from watchdog.events import RegexMatchingEventHandler
from watchdog.observers import Observer
from json import loads as json_decode
from json import dumps as json_encode
# ensure we are loading the config files nicely
from pywb import DEFAULT_CONFIG, DEFAULT_RULES_FILE, DEFAULT_CONFIG_FILE

six.moves.html_parser.unescape = lambda x: x

try:  # pragma: no cover
    import uwsgi

    uwsgi_cache = True
except ImportError:
    uwsgi_cache = False

if os.environ.get('GEVENT_MONKEY_PATCH') == '1':  # pragma: no cover
    # Use gevent if available
    try:
        from gevent.monkey import patch_all

        patch_all()
        print('gevent patched!')
    except Exception as e:
        pass

try:
    from boto import connect_s3

    s3_avail = True
except ImportError:  # pragma: no cover
    s3_avail = False

# Use ujson if available
try:
    from ujson import dumps as ujson_dumps

    try:
        assert (ujson_dumps('http://example.com/',
                            escape_forward_slashes=False) ==
                '"http://example.com/"')
    except Exception as e:  # pragma: no cover
        sys.stderr.write('ujson w/o forward-slash escaping not available,\
defaulting to regular json\n')
        raise


    def json_encode(obj):
        return ujson_dumps(obj, escape_forward_slashes=False)

except:  # pragma: no cover
    from json import dumps as json_encode

try:  # pragma: no cover
    from collections import OrderedDict
except ImportError:  # pragma: no cover
    from ordereddict import OrderedDict



# =============================================================================
EXT_REGEX = '.*\.w?arc(\.gz)?$'

keep_running = True

# =================================================================


DEFAULT_PORT = 8080

WRAP_WIDTH = 80

FILTERS = {}

# =================================================================


DATE_TIMESPLIT = re.compile(r'[^\d]')

TIMESTAMP_14 = '%Y%m%d%H%M%S'
ISO_DT = '%Y-%m-%dT%H:%M:%SZ'

PAD_14_DOWN = '10000101000000'
PAD_14_UP = '29991231235959'
PAD_6_UP = '299912'

LINK_FORMAT = 'application/link-format'

# =================================================================
URLKEY = 'urlkey'
TIMESTAMP = 'timestamp'
ORIGINAL = 'url'
MIMETYPE = 'mime'
STATUSCODE = 'status'
DIGEST = 'digest'
REDIRECT = 'redirect'
ROBOTFLAGS = 'robotflags'
LENGTH = 'length'
OFFSET = 'offset'
FILENAME = 'filename'

ORIG_LENGTH = 'orig.length'
ORIG_OFFSET = 'orig.offset'
ORIG_FILENAME = 'orig.filename'


# =================================================================
# begin pywb.utils.wbexception
class WbException(Exception):
    def __init__(self, msg=None, url=None):
        Exception.__init__(self, msg)
        self.msg = msg
        self.url = url


class AccessException(WbException):
    def status(self):
        return '403 Access Denied'


class BadRequestException(WbException):
    def status(self):
        return '400 Bad Request'


class NotFoundException(WbException):
    def status(self):
        return '404 Not Found'


class LiveResourceException(WbException):
    def status(self):
        return '400 Bad Live Resource'


class CDXException(WbException):
    def status(self):
        return '400 Bad Request'


# End pywb.utils.wbexception
# =================================================================

# =================================================================
# begin pywb.utils.loaders

# =================================================================
def is_http(filename):
    return filename.startswith(('http://', 'https://'))


# =================================================================
def to_file_url(filename):
    """ Convert a filename to a file:// url
    """
    url = os.path.abspath(filename)
    url = urljoin('file:', pathname2url(url))
    return url


# =================================================================
def load_yaml_config(config_file):
    config = None
    configdata = None
    try:
        configdata = BlockLoader().load(config_file)
        config = yaml.load(configdata)
    finally:
        configdata.close()
        if configdata:
            configdata.close()

    return config


# =================================================================
def to_native_str(value, encoding='iso-8859-1', func=lambda x: x):
    if isinstance(value, str):
        return value

    if six.PY3 and isinstance(value, six.binary_type):  # pragma: no cover
        return func(value.decode(encoding))
    elif six.PY2 and isinstance(value, six.text_type):  # pragma: no cover
        return func(value.encode(encoding))


# =================================================================
def extract_post_query(method, mime, length, stream,
                       buffered_stream=None,
                       environ=None):
    """
    Extract a url-encoded form POST from stream
    content length, return None
    Attempt to decode application/x-www-form-urlencoded or multipart/*,
    otherwise read whole block and b64encode
    """
    if method.upper() != 'POST':
        return None

    try:
        length = int(length)
    except (ValueError, TypeError):
        return None

    if length <= 0:
        return None

    post_query = b''

    while length > 0:
        buff = stream.read(length)
        length -= len(buff)

        if not buff:
            break

        post_query += buff

    if buffered_stream:
        buffered_stream.write(post_query)
        buffered_stream.seek(0)

    if not mime:
        mime = ''

    if mime.startswith('application/x-www-form-urlencoded'):
        post_query = to_native_str(post_query)
        post_query = unquote_plus(post_query)

    elif mime.startswith('multipart/'):
        env = {'REQUEST_METHOD': 'POST',
               'CONTENT_TYPE': mime,
               'CONTENT_LENGTH': len(post_query)}

        args = dict(fp=BytesIO(post_query),
                    environ=env,
                    keep_blank_values=True)

        if six.PY3:
            args['encoding'] = 'utf-8'

        data = cgi.FieldStorage(**args)

        values = []
        for item in data.list:
            values.append((item.name, item.value))

        post_query = urlencode(values, True)

    elif mime.startswith('application/x-amf'):
        post_query = amf_parse(post_query, environ)

    else:
        post_query = base64.b64encode(post_query)
        post_query = to_native_str(post_query)
        post_query = '&__wb_post_data=' + post_query

    return post_query


# =================================================================
def amf_parse(string, environ):
    try:
        from pyamf import remoting

        res = remoting.decode(BytesIO(string))

        # print(res)
        body = res.bodies[0][1].body[0]

        values = {}

        if hasattr(body, 'body'):
            values['body'] = body.body

        if hasattr(body, 'source'):
            values['source'] = body.source

        if hasattr(body, 'operation'):
            values['op'] = body.operation

        if environ is not None:
            environ['pywb.inputdata'] = res

        query = urlencode(values)
        # print(query)
        return query

    except Exception as e:
        import traceback
        traceback.print_exc()
        print(e)
        return None


# =================================================================
def append_post_query(url, post_query):
    if not post_query:
        return url

    if '?' not in url:
        url += '?'
    else:
        url += '&'

    url += post_query
    return url


# =================================================================
def extract_client_cookie(env, cookie_name):
    cookie_header = env.get('HTTP_COOKIE')
    if not cookie_header:
        return None

    # attempt to extract cookie_name only
    inx = cookie_header.find(cookie_name)
    if inx < 0:
        return None

    end_inx = cookie_header.find(';', inx)
    if end_inx > 0:
        value = cookie_header[inx:end_inx]
    else:
        value = cookie_header[inx:]

    value = value.split('=')
    if len(value) < 2:
        return None

    value = value[1].strip()
    return value


# =================================================================
def read_last_line(fh, offset=256):
    """ Read last line from a seekable file. Start reading
    from buff before end of file, and double backwards seek
    until line break is found. If reached beginning of file
    (no lines), just return whole file
    """
    fh.seek(0, 2)
    size = fh.tell()

    while offset < size:
        fh.seek(-offset, 2)
        lines = fh.readlines()
        if len(lines) > 1:
            return lines[-1]
        offset *= 2

    fh.seek(0, 0)
    return fh.readlines()[-1]


# =================================================================
class BaseLoader(object):
    def __init__(self, **kwargs):
        pass

    def load(self, url, offset=0, length=-1):
        raise NotImplemented()


# =================================================================
class BlockLoader(BaseLoader):
    """
    a loader which can stream blocks of content
    given a uri, offset and optional length.
    Currently supports: http/https and file/local file system
    """

    loaders = {}
    profile_loader = None

    def __init__(self, **kwargs):
        self.cached = {}
        self.kwargs = kwargs

    def load(self, url, offset=0, length=-1):
        loader, url = self._get_loader_for_url(url)
        return loader.load(url, offset, length)

    def _get_loader_for_url(self, url):
        """
        Determine loading method based on uri
        """
        parts = url.split('://', 1)
        if len(parts) < 2:
            type_ = 'file'
        else:
            type_ = parts[0]

        if '+' in type_:
            profile_name, scheme = type_.split('+', 1)
            if len(parts) == 2:
                url = scheme + '://' + parts[1]
        else:
            profile_name = ''
            scheme = type_

        loader = self.cached.get(type_)
        if loader:
            return loader, url

        loader_cls = self._get_loader_class_for_type(scheme)

        if not loader_cls:
            raise IOError('No Loader for type: ' + scheme)

        profile = self.kwargs

        if self.profile_loader:
            profile = self.profile_loader(profile_name, scheme)

        loader = loader_cls(**profile)

        self.cached[type_] = loader
        return loader, url

    def _get_loader_class_for_type(self, type_):
        loader_cls = self.loaders.get(type_)
        return loader_cls

    @staticmethod
    def init_default_loaders():
        BlockLoader.loaders['http'] = HttpLoader
        BlockLoader.loaders['https'] = HttpLoader
        BlockLoader.loaders['s3'] = S3Loader
        BlockLoader.loaders['file'] = LocalFileLoader

    @staticmethod
    def set_profile_loader(src):
        BlockLoader.profile_loader = src

    @staticmethod
    def _make_range_header(offset, length):
        if length > 0:
            range_header = 'bytes={0}-{1}'.format(offset, offset + length - 1)
        else:
            range_header = 'bytes={0}-'.format(offset)

        return range_header


# =================================================================
class LocalFileLoader(BaseLoader):
    def load(self, url, offset=0, length=-1):
        """
        Load a file-like reader from the local file system
        """

        # if starting with . or /, can only be a file path..
        file_only = url.startswith(('/', '.'))

        # convert to filename
        if url.startswith('file://'):
            file_only = True
            url = url2pathname(url[len('file://'):])

        try:
            # first, try as file
            afile = open(url, 'rb')

        except IOError:
            if file_only:
                raise

            # then, try as package.path/file
            pkg_split = url.split('/', 1)
            if len(pkg_split) == 1:
                raise

            afile = pkg_resources.resource_stream(pkg_split[0],
                                                  pkg_split[1])

        if offset > 0:
            afile.seek(offset)

        if length >= 0:
            return LimitReader(afile, length)
        else:
            return afile


# =================================================================
class HttpLoader(BaseLoader):
    def __init__(self, **kwargs):
        self.cookie_maker = kwargs.get('cookie_maker')
        if not self.cookie_maker:
            self.cookie_maker = kwargs.get('cookie')
        self.session = None

    def load(self, url, offset, length):
        """
        Load a file-like reader over http using range requests
        and an optional cookie created via a cookie_maker
        """
        headers = {}
        if offset != 0 or length != -1:
            headers['Range'] = BlockLoader._make_range_header(offset, length)

        if self.cookie_maker:
            if isinstance(self.cookie_maker, six.string_types):
                headers['Cookie'] = self.cookie_maker
            else:
                headers['Cookie'] = self.cookie_maker.make()

        if not self.session:
            self.session = requests.Session()

        r = self.session.get(url, headers=headers, stream=True)
        return r.raw


# =================================================================
class S3Loader(BaseLoader):
    def __init__(self, **kwargs):
        self.s3conn = None
        self.aws_access_key_id = kwargs.get('aws_access_key_id')
        self.aws_secret_access_key = kwargs.get('aws_secret_access_key')

    def load(self, url, offset, length):
        if not s3_avail:  # pragma: no cover
            raise IOError('To load from s3 paths, ' +
                          'you must install boto: pip install boto')

        aws_access_key_id = self.aws_access_key_id
        aws_secret_access_key = self.aws_secret_access_key

        parts = urlsplit(url)

        if parts.username and parts.password:
            aws_access_key_id = unquote_plus(parts.username)
            aws_secret_access_key = unquote_plus(parts.password)
            bucket_name = parts.netloc.split('@', 1)[-1]
        else:
            bucket_name = parts.netloc

        if not self.s3conn:
            try:
                self.s3conn = connect_s3(aws_access_key_id, aws_secret_access_key)
            except Exception:  # pragma: no cover
                self.s3conn = connect_s3(anon=True)

        bucket = self.s3conn.get_bucket(bucket_name)

        key = bucket.get_key(parts.path)

        if offset == 0 and length == -1:
            headers = {}
        else:
            headers = {'Range': BlockLoader._make_range_header(offset, length)}

        # Read range
        key.open_read(headers=headers)
        return key


# =================================================================
# Signed Cookie-Maker
# =================================================================

class HMACCookieMaker(object):
    """
    Utility class to produce signed HMAC digest cookies
    to be used with each http request
    """

    def __init__(self, key, name, duration=10):
        self.key = key
        self.name = name
        # duration in seconds
        self.duration = duration

    def make(self, extra_id=''):
        expire = str(int(time.time() + self.duration))

        if extra_id:
            msg = extra_id + '-' + expire
        else:
            msg = expire

        hmacdigest = hmac.new(self.key.encode('utf-8'), msg.encode('utf-8'))
        hexdigest = hmacdigest.hexdigest()

        if extra_id:
            cookie = '{0}-{1}={2}-{3}'.format(self.name, extra_id,
                                              expire, hexdigest)
        else:
            cookie = '{0}={1}-{2}'.format(self.name, expire, hexdigest)

        return cookie


# =================================================================
# Limit Reader
# =================================================================
class LimitReader(object):
    """
    A reader which will not read more than specified limit
    """

    def __init__(self, stream, limit):
        self.stream = stream
        self.limit = limit

    def read(self, length=None):
        if length is not None:
            length = min(length, self.limit)
        else:
            length = self.limit

        if length == 0:
            return b''

        buff = self.stream.read(length)
        self.limit -= len(buff)
        return buff

    def readline(self, length=None):
        if length is not None:
            length = min(length, self.limit)
        else:
            length = self.limit

        if length == 0:
            return b''

        buff = self.stream.readline(length)
        self.limit -= len(buff)
        return buff

    def close(self):
        self.stream.close()

    @staticmethod
    def wrap_stream(stream, content_length):
        """
        If given content_length is an int > 0, wrap the stream
        in a LimitReader. Otherwise, return the stream unaltered
        """
        try:
            content_length = int(content_length)
            if content_length >= 0:
                # optimize: if already a LimitStream, set limit to
                # the smaller of the two limits
                if isinstance(stream, LimitReader):
                    stream.limit = min(stream.limit, content_length)
                else:
                    stream = LimitReader(stream, content_length)

        except (ValueError, TypeError):
            pass

        return stream



BlockLoader.init_default_loaders()

# ============================================================================

# end pywb.utils.loaders
# ============================================================================


# begin pywb.utils.timeutils

def iso_date_to_datetime(string):
    """
    >>> iso_date_to_datetime('2013-12-26T10:11:12Z')
    datetime.datetime(2013, 12, 26, 10, 11, 12)

    >>> iso_date_to_datetime('2013-12-26T10:11:12Z')
    datetime.datetime(2013, 12, 26, 10, 11, 12)
     """

    nums = DATE_TIMESPLIT.split(string)
    if nums[-1] == '':
        nums = nums[:-1]

    the_datetime = datetime.datetime(*map(int, nums))
    return the_datetime


def http_date_to_datetime(string):
    """
    >>> http_date_to_datetime('Thu, 26 Dec 2013 09:50:10 GMT')
    datetime.datetime(2013, 12, 26, 9, 50, 10)
    """
    return datetime.datetime(*parsedate(string)[:6])


def datetime_to_http_date(the_datetime):
    """
    >>> datetime_to_http_date(datetime.datetime(2013, 12, 26, 9, 50, 10))
    'Thu, 26 Dec 2013 09:50:10 GMT'

    # Verify inverses
    >>> x = 'Thu, 26 Dec 2013 09:50:10 GMT'
    >>> datetime_to_http_date(http_date_to_datetime(x)) == x
    True
    """
    timeval = calendar.timegm(the_datetime.utctimetuple())
    return formatdate(timeval=timeval,
                      localtime=False,
                      usegmt=True)


def datetime_to_iso_date(the_datetime):
    """
    >>> datetime_to_iso_date(datetime.datetime(2013, 12, 26, 10, 11, 12))
    '2013-12-26T10:11:12Z'

    >>> datetime_to_iso_date( datetime.datetime(2013, 12, 26, 10, 11, 12))
    '2013-12-26T10:11:12Z'
    """

    return the_datetime.strftime(ISO_DT)


def datetime_to_timestamp(the_datetime):
    """
    >>> datetime_to_timestamp(datetime.datetime(2013, 12, 26, 10, 11, 12))
    '20131226101112'
    """

    return the_datetime.strftime(TIMESTAMP_14)


def timestamp_now():
    """
    >>> len(timestamp_now())
    14
    """
    return datetime_to_timestamp(datetime.datetime.utcnow())


def timestamp20_now():
    """
    Create 20-digit timestamp, useful to timestamping temp files

    >>> n = timestamp20_now()
    >>> timestamp20_now() >= n
    True

    >>> len(n)
    20

    """
    now = datetime.datetime.utcnow()
    return now.strftime('%Y%m%d%H%M%S%f')


def iso_date_to_timestamp(string):
    """
    >>> iso_date_to_timestamp('2013-12-26T10:11:12Z')
    '20131226101112'

    >>> iso_date_to_timestamp('2013-12-26T10:11:12')
    '20131226101112'
     """

    return datetime_to_timestamp(iso_date_to_datetime(string))


def http_date_to_timestamp(string):
    """
    >>> http_date_to_timestamp('Thu, 26 Dec 2013 09:50:00 GMT')
    '20131226095000'

    >>> http_date_to_timestamp('Sun, 26 Jan 2014 20:08:04 GMT')
    '20140126200804'
    """
    return datetime_to_timestamp(http_date_to_datetime(string))


# pad to certain length (default 6)
def pad_timestamp(string, pad_str=PAD_6_UP):
    """
    >>> pad_timestamp('20')
    '209912'

    >>> pad_timestamp('2014')
    '201412'

    >>> pad_timestamp('20141011')
    '20141011'

    >>> pad_timestamp('201410110010')
    '201410110010'
     """

    str_len = len(string)
    pad_len = len(pad_str)

    if str_len < pad_len:
        string = string + pad_str[str_len:]

    return string


def timestamp_to_datetime(string):
    """
    # >14-digit -- rest ignored
    >>> timestamp_to_datetime('2014122609501011')
    datetime.datetime(2014, 12, 26, 9, 50, 10)

    # 14-digit
    >>> timestamp_to_datetime('20141226095010')
    datetime.datetime(2014, 12, 26, 9, 50, 10)

    # 13-digit padding
    >>> timestamp_to_datetime('2014122609501')
    datetime.datetime(2014, 12, 26, 9, 50, 59)

    # 12-digit padding
    >>> timestamp_to_datetime('201412260950')
    datetime.datetime(2014, 12, 26, 9, 50, 59)

    # 11-digit padding
    >>> timestamp_to_datetime('20141226095')
    datetime.datetime(2014, 12, 26, 9, 59, 59)

    # 10-digit padding
    >>> timestamp_to_datetime('2014122609')
    datetime.datetime(2014, 12, 26, 9, 59, 59)

    # 9-digit padding
    >>> timestamp_to_datetime('201412260')
    datetime.datetime(2014, 12, 26, 23, 59, 59)

    # 8-digit padding
    >>> timestamp_to_datetime('20141226')
    datetime.datetime(2014, 12, 26, 23, 59, 59)

    # 7-digit padding
    >>> timestamp_to_datetime('2014122')
    datetime.datetime(2014, 12, 31, 23, 59, 59)

    # 6-digit padding
    >>> timestamp_to_datetime('201410')
    datetime.datetime(2014, 10, 31, 23, 59, 59)

    # 5-digit padding
    >>> timestamp_to_datetime('20141')
    datetime.datetime(2014, 12, 31, 23, 59, 59)

    # 4-digit padding
    >>> timestamp_to_datetime('2014')
    datetime.datetime(2014, 12, 31, 23, 59, 59)

    # 3-digit padding
    >>> timestamp_to_datetime('201')
    datetime.datetime(2019, 12, 31, 23, 59, 59)

    # 2-digit padding
    >>> timestamp_to_datetime('20')
    datetime.datetime(2099, 12, 31, 23, 59, 59)

    # 1-digit padding
    >>> timestamp_to_datetime('2')
    datetime.datetime(2999, 12, 31, 23, 59, 59)

    # 1-digit out-of-range padding
    >>> timestamp_to_datetime('3')
    datetime.datetime(2999, 12, 31, 23, 59, 59)

    # 0-digit padding
    >>> timestamp_to_datetime('')
    datetime.datetime(2999, 12, 31, 23, 59, 59)

    # bad month
    >>> timestamp_to_datetime('20131709005601')
    datetime.datetime(2013, 12, 9, 0, 56, 1)

    # all out of range except minutes
    >>> timestamp_to_datetime('40001965252477')
    datetime.datetime(2999, 12, 31, 23, 24, 59)

    # not a number!
    >>> timestamp_to_datetime('2010abc')
    datetime.datetime(2010, 12, 31, 23, 59, 59)

    """

    # pad to 6 digits
    string = pad_timestamp(string, PAD_6_UP)

    def clamp(val, min_, max_):
        try:
            val = int(val)
            val = max(min_, min(val, max_))
            return val
        except:
            return max_

    def extract(string, start, end, min_, max_):
        if len(string) >= end:
            return clamp(string[start:end], min_, max_)
        else:
            return max_

    # now parse, clamp to boundary
    year = extract(string, 0, 4, 1900, 2999)
    month = extract(string, 4, 6, 1, 12)
    day = extract(string, 6, 8, 1, calendar.monthrange(year, month)[1])
    hour = extract(string, 8, 10, 0, 23)
    minute = extract(string, 10, 12, 0, 59)
    second = extract(string, 12, 14, 0, 59)

    return datetime.datetime(year=year,
                             month=month,
                             day=day,
                             hour=hour,
                             minute=minute,
                             second=second)

    # return time.strptime(pad_timestamp(string), TIMESTAMP_14)


def timestamp_to_sec(string):
    """
    >>> timestamp_to_sec('20131226095010')
    1388051410

    # rounds to end of 2014
    >>> timestamp_to_sec('2014')
    1420070399
    """

    return calendar.timegm(timestamp_to_datetime(string).utctimetuple())


def sec_to_timestamp(secs):
    """
    >>> sec_to_timestamp(1388051410)
    '20131226095010'

    >>> sec_to_timestamp(1420070399)
    '20141231235959'
    """

    return datetime_to_timestamp(datetime.datetime.utcfromtimestamp(secs))


def timestamp_to_http_date(string):
    """
    >>> timestamp_to_http_date('20131226095000')
    'Thu, 26 Dec 2013 09:50:00 GMT'

    >>> timestamp_to_http_date('20140126200804')
    'Sun, 26 Jan 2014 20:08:04 GMT'
    """
    return datetime_to_http_date(timestamp_to_datetime(string))


# end pywb.utils.timeutils

# begin pywb.utils.statusandheaders
# =================================================================
class StatusAndHeaders(object):
    """
    Representation of parsed http-style status line and headers
    Status Line if first line of request/response
    Headers is a list of (name, value) tuples
    An optional protocol which appears on first line may be specified
    """

    def __init__(self, statusline, headers, protocol='', total_len=0):
        self.statusline = statusline
        self.headers = headers
        self.protocol = protocol
        self.total_len = total_len

    def get_header(self, name):
        """
        return header (name, value)
        if found
        """
        name_lower = name.lower()
        for value in self.headers:
            if value[0].lower() == name_lower:
                return value[1]

    def replace_header(self, name, value):
        """
        replace header with new value or add new header
        return old header value, if any
        """
        name_lower = name.lower()
        for index in range(len(self.headers) - 1, -1, -1):
            curr_name, curr_value = self.headers[index]
            if curr_name.lower() == name_lower:
                self.headers[index] = (curr_name, value)
                return curr_value

        self.headers.append((name, value))
        return None

    def replace_headers(self, header_dict):
        """
        replace all headers in header_dict that already exist
        add any remaining headers
        """
        header_dict = copy(header_dict)

        for index in range(len(self.headers) - 1, -1, -1):
            curr_name, curr_value = self.headers[index]
            name_lower = curr_name.lower()
            if name_lower in header_dict:
                self.headers[index] = (curr_name, header_dict[name_lower])
                del header_dict[name_lower]

        for name, value in iteritems(header_dict):
            self.headers.append((name, value))

    def remove_header(self, name):
        """
        Remove header (case-insensitive)
        return True if header removed, False otherwise
        """
        name_lower = name.lower()
        for index in range(len(self.headers) - 1, -1, -1):
            if self.headers[index][0].lower() == name_lower:
                del self.headers[index]
                return True

        return False

    def get_statuscode(self):
        """
        Return the statuscode part of the status response line
        (Assumes no protocol in the statusline)
        """
        code = self.statusline.split(' ', 1)[0]
        return code

    def validate_statusline(self, valid_statusline):
        """
        Check that the statusline is valid, eg. starts with a numeric
        code. If not, replace with passed in valid_statusline
        """
        code = self.get_statuscode()
        try:
            code = int(code)
            assert (code > 0)
            return True
        except(ValueError, AssertionError):
            self.statusline = valid_statusline
            return False

    def add_range(self, start, part_len, total_len):
        """
        Add range headers indicating that this a partial response
        """
        content_range = 'bytes {0}-{1}/{2}'.format(start,
                                                   start + part_len - 1,
                                                   total_len)

        self.statusline = '206 Partial Content'
        self.replace_header('Content-Range', content_range)
        self.replace_header('Accept-Ranges', 'bytes')
        return self

    def __repr__(self):
        headers_str = pformat(self.headers, indent=2, width=WRAP_WIDTH)
        return "StatusAndHeaders(protocol = '{0}', statusline = '{1}', \
headers = {2})".format(self.protocol, self.statusline, headers_str)

    def __eq__(self, other):
        return (self.statusline == other.statusline and
                self.headers == other.headers and
                self.protocol == other.protocol)

    def __str__(self, exclude_list=None):
        return self.to_str(exclude_list)

    def to_str(self, exclude_list):
        string = self.protocol

        if string and self.statusline:
            string += ' '

        if self.statusline:
            string += self.statusline

        if string:
            string += '\r\n'

        for h in self.headers:
            if exclude_list and h[0].lower() in exclude_list:
                continue

            string += ': '.join(h) + '\r\n'

        return string

    def to_bytes(self, exclude_list=None):
        return self.to_str(exclude_list).encode('iso-8859-1') + b'\r\n'


# =================================================================
def _strip_count(string, total_read):
    length = len(string)
    return string.rstrip(), total_read + length


# =================================================================
class StatusAndHeadersParser(object):
    """
    Parser which consumes a stream support readline() to read
    status and headers and return a StatusAndHeaders object
    """

    def __init__(self, statuslist, verify=True):
        self.statuslist = statuslist
        self.verify = verify

    def parse(self, stream, full_statusline=None):
        """
        parse stream for status line and headers
        return a StatusAndHeaders object

        support continuation headers starting with space or tab
        """

        def readline():
            return to_native_str(stream.readline())

        # status line w newlines intact
        if full_statusline is None:
            full_statusline = readline()
        else:
            full_statusline = to_native_str(full_statusline)

        statusline, total_read = _strip_count(full_statusline, 0)

        headers = []

        # at end of stream
        if total_read == 0:
            raise EOFError()
        elif not statusline:
            return StatusAndHeaders(statusline=statusline,
                                    headers=headers,
                                    protocol='',
                                    total_len=total_read)

        # validate only if verify is set
        if self.verify:
            protocol_status = self.split_prefix(statusline, self.statuslist)

            if not protocol_status:
                msg = 'Expected Status Line starting with {0} - Found: {1}'
                msg = msg.format(self.statuslist, statusline)
                raise StatusAndHeadersParserException(msg, full_statusline)
        else:
            protocol_status = statusline.split(' ', 1)

        line, total_read = _strip_count(readline(), total_read)
        while line:
            result = line.split(':', 1)
            if len(result) == 2:
                name = result[0].rstrip(' \t')
                value = result[1].lstrip()
            else:
                name = result[0]
                value = None

            next_line, total_read = _strip_count(readline(),
                                                 total_read)

            # append continuation lines, if any
            while next_line and next_line.startswith((' ', '\t')):
                if value is not None:
                    value += next_line
                next_line, total_read = _strip_count(readline(),
                                                     total_read)

            if value is not None:
                header = (name, value)
                headers.append(header)

            line = next_line

        if len(protocol_status) > 1:
            statusline = protocol_status[1].strip()
        else:
            statusline = ''

        return StatusAndHeaders(statusline=statusline,
                                headers=headers,
                                protocol=protocol_status[0],
                                total_len=total_read)

    @staticmethod
    def split_prefix(key, prefixs):
        """
        split key string into prefix and remainder
        for first matching prefix from a list
        """
        key_upper = key.upper()
        for prefix in prefixs:
            if key_upper.startswith(prefix):
                plen = len(prefix)
                return (key_upper[:plen], key[plen:])


# =================================================================
class StatusAndHeadersParserException(Exception):
    """
    status + headers parsing exception
    """

    def __init__(self, msg, statusline):
        super(StatusAndHeadersParserException, self).__init__(msg)
        self.statusline = statusline


# end pywb.utils.statusandheaders


# begin pywb.utils.bufferedreader

# =================================================================
def gzip_decompressor():
    """
    Decompressor which can handle decompress gzip stream
    """
    return zlib.decompressobj(16 + zlib.MAX_WBITS)


def deflate_decompressor():
    return zlib.decompressobj()


def deflate_decompressor_alt():
    return zlib.decompressobj(-zlib.MAX_WBITS)


def brotli_decompressor():
    decomp = brotli.Decompressor()
    decomp.unused_data = None
    return decomp


# =================================================================
class BufferedReader(object):
    """
    A wrapping line reader which wraps an existing reader.
    Read operations operate on underlying buffer, which is filled to
    block_size (1024 default)

    If an optional decompress type is specified,
    data is fed through the decompressor when read from the buffer.
    Currently supported decompression: gzip
    If unspecified, default decompression is None

    If decompression is specified, and decompress fails on first try,
    data is assumed to not be compressed and no exception is thrown.

    If a failure occurs after data has been
    partially decompressed, the exception is propagated.

    """

    DECOMPRESSORS = {'gzip': gzip_decompressor,
                     'deflate': deflate_decompressor,
                     'deflate_alt': deflate_decompressor_alt,
                     'br': brotli_decompressor
                     }

    def __init__(self, stream, block_size=1024,
                 decomp_type=None,
                 starting_data=None):
        self.stream = stream
        self.block_size = block_size

        self._init_decomp(decomp_type)

        self.buff = None
        self.starting_data = starting_data
        self.num_read = 0
        self.buff_size = 0

    def set_decomp(self, decomp_type):
        self._init_decomp(decomp_type)

    def _init_decomp(self, decomp_type):
        if decomp_type:
            try:
                self.decomp_type = decomp_type
                self.decompressor = self.DECOMPRESSORS[decomp_type.lower()]()
            except KeyError:
                raise Exception('Decompression type not supported: ' +
                                decomp_type)
        else:
            self.decomp_type = None
            self.decompressor = None

    def _fillbuff(self, block_size=None):
        if not self.empty():
            return

        # can't read past next member
        if self.rem_length() > 0:
            return

        if self.starting_data:
            data = self.starting_data
            self.starting_data = None
        else:
            if not block_size:
                block_size = self.block_size
            data = self.stream.read(block_size)

        self._process_read(data)

    def _process_read(self, data):
        data = self._decompress(data)
        self.buff_size = len(data)
        self.num_read += self.buff_size
        self.buff = BytesIO(data)

    def _decompress(self, data):
        if self.decompressor and data:
            try:
                data = self.decompressor.decompress(data)
            except Exception as e:
                # if first read attempt, assume non-gzipped stream
                if self.num_read == 0:
                    if self.decomp_type == 'deflate':
                        self._init_decomp('deflate_alt')
                        data = self._decompress(data)
                    else:
                        self.decompressor = None
                # otherwise (partly decompressed), something is wrong
                else:
                    print(str(e))
                    return b''
        return data

    def read(self, length=None):
        """
        Fill bytes and read some number of bytes
        (up to length if specified)
        < length bytes may be read if reached the end of input
        or at a buffer boundary. If at a boundary, the subsequent
        call will fill buffer anew.
        """
        if length == 0:
            return b''

        self._fillbuff()
        buff = self.buff.read(length)
        return buff

    def readline(self, length=None):
        """
        Fill buffer and read a full line from the buffer
        (up to specified length, if provided)
        If no newline found at end, try filling buffer again in case
        at buffer boundary.
        """
        if length == 0:
            return b''

        self._fillbuff()
        linebuff = self.buff.readline(length)

        # we may be at a boundary
        while not linebuff.endswith(b'\n'):
            if length:
                length -= len(linebuff)
                if length <= 0:
                    break

            self._fillbuff()

            if self.empty():
                break

            linebuff += self.buff.readline(length)

        return linebuff

    def empty(self):
        return not self.buff or self.buff.tell() >= self.buff_size

    def read_next_member(self):
        if not self.decompressor or not self.decompressor.unused_data:
            return False

        self.starting_data = self.decompressor.unused_data
        self._init_decomp(self.decomp_type)
        return True

    def rem_length(self):
        rem = 0
        if self.buff:
            rem = self.buff_size - self.buff.tell()

        if self.decompressor and self.decompressor.unused_data:
            rem += len(self.decompressor.unused_data)
        return rem

    def close(self):
        if self.stream:
            self.stream.close()
            self.stream = None

    @classmethod
    def get_supported_decompressors(cls):
        return cls.DECOMPRESSORS.keys()


# =================================================================
class DecompressingBufferedReader(BufferedReader):
    """
    A BufferedReader which defaults to gzip decompression,
    (unless different type specified)
    """

    def __init__(self, *args, **kwargs):
        if 'decomp_type' not in kwargs:
            kwargs['decomp_type'] = 'gzip'
        super(DecompressingBufferedReader, self).__init__(*args, **kwargs)


# =================================================================
class ChunkedDataException(Exception):
    def __init__(self, msg, data=b''):
        Exception.__init__(self, msg)
        self.data = data


# =================================================================
class ChunkedDataReader(BufferedReader):
    r"""
    A ChunkedDataReader is a DecompressingBufferedReader
    which also supports de-chunking of the data if it happens
    to be http 'chunk-encoded'.

    If at any point the chunked header is not available, the stream is
    assumed to not be chunked and no more dechunking occurs.
    """

    def __init__(self, stream, raise_exceptions=False, **kwargs):
        super(ChunkedDataReader, self).__init__(stream, **kwargs)
        self.all_chunks_read = False
        self.not_chunked = False

        # if False, we'll use best-guess fallback for parse errors
        self.raise_chunked_data_exceptions = raise_exceptions

    def _fillbuff(self, block_size=None):
        if self.not_chunked:
            return super(ChunkedDataReader, self)._fillbuff(block_size)

        # Loop over chunks until there is some data (not empty())
        # In particular, gzipped data may require multiple chunks to
        # return any decompressed result
        while (self.empty() and
                   not self.all_chunks_read and
                   not self.not_chunked):

            try:
                length_header = self.stream.readline(64)
                self._try_decode(length_header)
            except ChunkedDataException as e:
                if self.raise_chunked_data_exceptions:
                    raise

                # Can't parse the data as chunked.
                # It's possible that non-chunked data is served
                # with a Transfer-Encoding: chunked.
                # Treat this as non-chunk encoded from here on.
                self._process_read(length_header + e.data)
                self.not_chunked = True

                # parse as block as non-chunked
                return super(ChunkedDataReader, self)._fillbuff(block_size)

    def _try_decode(self, length_header):
        # decode length header
        try:
            chunk_size = int(length_header.strip().split(b';')[0], 16)
        except ValueError:
            raise ChunkedDataException(b"Couldn't decode length header " +
                                       length_header)

        if not chunk_size:
            # chunk_size 0 indicates end of file
            self.all_chunks_read = True
            self._process_read(b'')
            return

        data_len = 0
        data = b''

        # read chunk
        while data_len < chunk_size:
            new_data = self.stream.read(chunk_size - data_len)

            # if we unexpectedly run out of data,
            # either raise an exception or just stop reading,
            # assuming file was cut off
            if not new_data:
                if self.raise_chunked_data_exceptions:
                    msg = 'Ran out of data before end of chunk'
                    raise ChunkedDataException(msg, data)
                else:
                    chunk_size = data_len
                    self.all_chunks_read = True

            data += new_data
            data_len = len(data)

        # if we successfully read a block without running out,
        # it should end in \r\n
        if not self.all_chunks_read:
            clrf = self.stream.read(2)
            if clrf != b'\r\n':
                raise ChunkedDataException(b"Chunk terminator not found.",
                                           data)

        # hand to base class for further processing
        self._process_read(data)

    def read(self, length=None):
        """ read bytes from stream, if length specified,
        may read across multiple chunks to get exact length
        """
        buf = super(ChunkedDataReader, self).read(length)
        if not length:
            return buf

        # if length specified, attempt to read exact length
        rem = length - len(buf)
        while rem > 0:
            new_buf = super(ChunkedDataReader, self).read(rem)
            if not new_buf:
                break

            buf += new_buf
            rem -= len(new_buf)

        return buf


# end pywb.utils.bufferedreader

# begin pywb.utils.dsrules

# =================================================================
class RuleSet(object):
    DEFAULT_KEY = ''

    def __init__(self, rule_cls, fieldname, **kwargs):
        """
        A domain specific rules block, inited via config map.
        If config map not specified, it is loaded from default location.

        The rules are represented as a map by domain.
        Each rules configuration will load is own field type
        from the list and given a specified rule_cls.
        """

        self.rules = []

        default_rule_config = kwargs.get('default_rule_config')

        ds_rules_file = kwargs.get('ds_rules_file')

        if not ds_rules_file:
            ds_rules_file = DEFAULT_RULES_FILE

        config = load_yaml_config(ds_rules_file)

        # load rules dict or init to empty
        rulesmap = config.get('rules') if config else {}

        def_key_found = False

        # iterate over master rules file
        for value in rulesmap:
            url_prefix = value.get('url_prefix')
            rules_def = value.get(fieldname)
            if not rules_def:
                continue

            if url_prefix == self.DEFAULT_KEY:
                def_key_found = True

            self.rules.append(rule_cls(url_prefix, rules_def))

        # if default_rule_config provided, always init a default ruleset
        if not def_key_found and default_rule_config is not None:
            self.rules.append(rule_cls(self.DEFAULT_KEY, default_rule_config))

    def iter_matching(self, urlkey):
        """
        Iterate over all matching rules for given urlkey
        """
        for rule in self.rules:
            if rule.applies(urlkey):
                yield rule

    def get_first_match(self, urlkey):
        for rule in self.rules:
            if rule.applies(urlkey):
                return rule


# =================================================================
class BaseRule(object):
    """
    Base rule class -- subclassed to handle specific
    rules for given url_prefix key
    """

    def __init__(self, url_prefix, rules):
        self.url_prefix = url_prefix
        if not isinstance(self.url_prefix, list):
            self.url_prefix = [self.url_prefix]

    def applies(self, urlkey):
        return any(urlkey.startswith(x) for x in self.url_prefix)


# end pywb.utils.dsrules


# begin pywb.utils.binsearch
if six.PY3:
    def cmp(a, b):
        return (a > b) - (a < b)


# =================================================================
def binsearch_offset(reader, key, compare_func=cmp, block_size=8192):
    """
    Find offset of the line which matches a given 'key' using binary search
    If key is not found, the offset is of the line after the key

    File is subdivided into block_size (default 8192) sized blocks
    Optional compare_func may be specified
    """
    min_ = 0

    reader.seek(0, 2)
    max_ = int(reader.tell() / block_size)

    while max_ - min_ > 1:
        mid = int(min_ + ((max_ - min_) / 2))
        reader.seek(mid * block_size)

        if mid > 0:
            reader.readline()  # skip partial line

        line = reader.readline()

        if compare_func(key, line) > 0:
            min_ = mid
        else:
            max_ = mid

    return min_ * block_size


# =================================================================
def binsearch(reader, key, compare_func=cmp, block_size=8192):
    """
    Perform a binary search for a specified key to within a 'block_size'
    (default 8192) granularity, and return first full line found.
    """

    min_ = binsearch_offset(reader, key, compare_func, block_size)

    reader.seek(min_)

    if min_ > 0:
        reader.readline()  # skip partial line

    def gen_iter(line):
        while line:
            yield line.rstrip()
            line = reader.readline()

    return gen_iter(reader.readline())


# =================================================================
def linearsearch(iter_, key, prev_size=0, compare_func=cmp):
    """
    Perform a linear search over iterator until
    current_line >= key

    optionally also tracking upto N previous lines, which are
    returned before the first matched line.

    if end of stream is reached before a match is found,
    nothing is returned (prev lines discarded also)
    """

    prev_deque = deque(maxlen=prev_size + 1)

    matched = False

    for line in iter_:
        prev_deque.append(line)
        if compare_func(line, key) >= 0:
            matched = True
            break

    # no matches, so return empty iterator
    if not matched:
        return iter([])

    return itertools.chain(prev_deque, iter_)


# =================================================================
def search(reader, key, prev_size=0, compare_func=cmp, block_size=8192):
    """
    Perform a binary search for a specified key to within a 'block_size'
    (default 8192) sized block followed by linear search
    within the block to find first matching line.

    When performin_g linear search, keep track of up to N previous lines before
    first matching line.
    """
    iter_ = binsearch(reader, key, compare_func, block_size)
    iter_ = linearsearch(iter_,
                         key, prev_size=prev_size,
                         compare_func=compare_func)
    return iter_


# =================================================================
def iter_range(reader, start, end, prev_size=0):
    """
    Creates an iterator which iterates over lines where
    start <= line < end (end exclusive)
    """

    iter_ = search(reader, start, prev_size=prev_size)

    end_iter = itertools.takewhile(
        lambda line: line < end,
        iter_)

    return end_iter


# =================================================================
def iter_prefix(reader, key):
    """
    Creates an iterator which iterates over lines that start with prefix
    'key' in a sorted text file.
    """

    return itertools.takewhile(
        lambda line: line.startswith(key),
        search(reader, key))


# =================================================================
def iter_exact(reader, key, token=b' '):
    """
    Create an iterator which iterates over lines where the first field matches
    the 'key', equivalent to token + sep prefix.
    Default field termin_ator/seperator is ' '
    """

    return iter_prefix(reader, key + token)


# end pywb.utils.binsearch


# begin pywb.utils.canonicalize
# =================================================================
class UrlCanonicalizer(object):
    def __init__(self, surt_ordered=True):
        self.surt_ordered = surt_ordered

    def __call__(self, url):
        return canonicalize(url, self.surt_ordered)


# =================================================================
class UrlCanonicalizeException(BadRequestException):
    pass


# =================================================================
def canonicalize(url, surt_ordered=True):
    """
    Canonicalize url and convert to surt
    If not in surt ordered mode, convert back to url form
    as surt conversion is currently part of canonicalization

    >>> canonicalize('http://example.com/path/file.html', surt_ordered=True)
    'com,example)/path/file.html'

    >>> canonicalize('http://example.com/path/file.html', surt_ordered=False)
    'example.com/path/file.html'

    >>> canonicalize('urn:some:id')
    'urn:some:id'
    """
    try:
        key = surt.surt(url)
    except Exception as e:  # pragma: no cover
        # doesn't happen with surt from 0.3b
        # urn is already canonical, so just use as-is
        if url.startswith('urn:'):
            return url

        raise UrlCanonicalizeException('Invalid Url: ' + url)

    # if not surt, unsurt the surt to get canonicalized non-surt url
    if not surt_ordered:
        key = unsurt(key)

    return key


# =================================================================
def unsurt(surt):
    """
    # Simple surt
    >>> unsurt('com,example)/')
    'example.com/'

    # Broken surt
    >>> unsurt('com,example)')
    'com,example)'

    # Long surt
    >>> unsurt('suffix,domain,sub,subsub,another,subdomain)/path/file/index.html?a=b?c=)/')
    'subdomain.another.subsub.sub.domain.suffix/path/file/index.html?a=b?c=)/'
    """

    try:
        index = surt.index(')/')
        parts = surt[0:index].split(',')
        parts.reverse()
        host = '.'.join(parts)
        host += surt[index + 1:]
        return host

    except ValueError:
        # May not be a valid surt
        return surt


# =================================================================
def calc_search_range(url, match_type, surt_ordered=True, url_canon=None):
    """
    Canonicalize a url (either with custom canonicalizer or
    standard canonicalizer with or without surt)

    Then, compute a start and end search url search range
    for a given match type.

    Support match types:
    * exact
    * prefix
    * host
    * domain (only available when for surt ordering)

    Examples below:

    # surt ranges
    >>> calc_search_range('http://example.com/path/file.html', 'exact')
    ('com,example)/path/file.html', 'com,example)/path/file.html!')

    >>> calc_search_range('http://example.com/path/file.html', 'prefix')
    ('com,example)/path/file.html', 'com,example)/path/file.htmm')

    >>> calc_search_range('http://example.com/path/file.html', 'host')
    ('com,example)/', 'com,example*')

    >>> calc_search_range('http://example.com/path/file.html', 'domain')
    ('com,example)/', 'com,example-')

    special case for tld domain range
    >>> calc_search_range('com', 'domain')
    ('com,', 'com-')

    # non-surt ranges
    >>> calc_search_range('http://example.com/path/file.html', 'exact', False)
    ('example.com/path/file.html', 'example.com/path/file.html!')

    >>> calc_search_range('http://example.com/path/file.html', 'prefix', False)
    ('example.com/path/file.html', 'example.com/path/file.htmm')

    >>> calc_search_range('http://example.com/path/file.html', 'host', False)
    ('example.com/', 'example.com0')

    # errors: domain range not supported
    >>> calc_search_range('http://example.com/path/file.html', 'domain', False)  # doctest: +IGNORE_EXCEPTION_DETAIL
    Traceback (most recent call last):
    UrlCanonicalizeException: matchType=domain unsupported for non-surt

    >>> calc_search_range('http://example.com/path/file.html', 'blah', False)   # doctest: +IGNORE_EXCEPTION_DETAIL
    Traceback (most recent call last):
    UrlCanonicalizeException: Invalid match_type: blah

    """

    def inc_last_char(x):
        return x[0:-1] + chr(ord(x[-1]) + 1)

    if not url_canon:
        # make new canon
        url_canon = UrlCanonicalizer(surt_ordered)
    else:
        # ensure surt order matches url_canon
        surt_ordered = url_canon.surt_ordered

    start_key = url_canon(url)

    if match_type == 'exact':
        end_key = start_key + '!'

    elif match_type == 'prefix':
        # add trailing slash if url has it
        if url.endswith('/') and not start_key.endswith('/'):
            start_key += '/'

        end_key = inc_last_char(start_key)

    elif match_type == 'host':
        if surt_ordered:
            host = start_key.split(')/')[0]

            start_key = host + ')/'
            end_key = host + '*'
        else:
            host = urlparse.urlsplit(url).netloc

            start_key = host + '/'
            end_key = host + '0'

    elif match_type == 'domain':
        if not surt_ordered:
            msg = 'matchType=domain unsupported for non-surt'
            raise UrlCanonicalizeException(msg)

        host = start_key.split(')/')[0]

        # if tld, use com, as start_key
        # otherwise, stick with com,example)/
        if ',' not in host:
            start_key = host + ','
        else:
            start_key = host + ')/'

        end_key = host + '-'
    else:
        raise UrlCanonicalizeException('Invalid match_type: ' + match_type)

    return (start_key, end_key)


# end pywb.utils.canonicalize


# begin pywb.framework.wbrequestresponse
# =================================================================
class WbRequest(object):
    """
    Represents the main pywb request object.

    Contains various info from wsgi env, add additional info
    about the request, such as coll, relative prefix,
    host prefix, absolute prefix.

    If a wburl and url rewriter classes are specified, the class
    also contains the url rewriter.

    """

    @staticmethod
    def make_host_prefix(env):
        try:
            host = env.get('HTTP_HOST')
            if not host:
                host = env['SERVER_NAME'] + ':' + env['SERVER_PORT']

            return env.get('wsgi.url_scheme', 'http') + '://' + host
        except KeyError:
            return ''

    def __init__(self, env,
                 request_uri=None,
                 rel_prefix='',
                 wb_url_str='/',
                 coll='',
                 host_prefix='',
                 use_abs_prefix=False,
                 wburl_class=None,
                 urlrewriter_class=None,
                 is_proxy=False,
                 cookie_scope=None,
                 rewrite_opts={},
                 user_metadata={},
                 ):

        self.env = env

        if request_uri:
            self.request_uri = request_uri
        else:
            self.request_uri = env.get('REL_REQUEST_URI')

        self.method = self.env.get('REQUEST_METHOD')

        self.coll = coll

        self.final_mod = ''

        if not host_prefix:
            host_prefix = self.make_host_prefix(env)

        self.host_prefix = host_prefix
        self.rel_prefix = rel_prefix

        if use_abs_prefix:
            self.wb_prefix = host_prefix + rel_prefix
        else:
            self.wb_prefix = rel_prefix

        if not wb_url_str:
            wb_url_str = '/'

        self.wb_url_str = wb_url_str

        # wb_url present and not root page
        if wb_url_str != '/' and wburl_class:
            self.wb_url = wburl_class(wb_url_str)
            self.urlrewriter = urlrewriter_class(self.wb_url,
                                                 self.wb_prefix,
                                                 host_prefix + rel_prefix,
                                                 rel_prefix,
                                                 env.get('SCRIPT_NAME', '/'),
                                                 cookie_scope,
                                                 rewrite_opts)

            self.urlrewriter.deprefix_url()
        # no wb_url, just store blank wb_url
        else:
            self.wb_url = None
            self.urlrewriter = None

        self.referrer = env.get('HTTP_REFERER')

        self.options = dict()
        self.options['is_ajax'] = self._is_ajax()
        self.options['is_proxy'] = is_proxy or env.get('pywb_proxy_magic')

        self.query_filter = []
        self.custom_params = {}
        self.user_metadata = user_metadata
        self.rewrite_opts = rewrite_opts

        # PERF
        env['X_PERF'] = {}

        if env.get('HTTP_X_PYWB_NOREDIRECT'):
            self.custom_params['noredir'] = True

        self._parse_extra()

    def _is_ajax(self):
        value = self.env.get('HTTP_X_REQUESTED_WITH')
        value = value or self.env.get('HTTP_X_PYWB_REQUESTED_WITH')
        if value and value.lower() == 'xmlhttprequest':
            return True

        return False

    RANGE_ARG_RX = re.compile('.*.googlevideo.com/videoplayback.*([&?]range=(\d+)-(\d+))')

    RANGE_HEADER = re.compile('bytes=(\d+)-(\d+)?')

    def extract_range(self):
        url = self.wb_url.url
        use_206 = False
        start = None
        end = None

        range_h = self.env.get('HTTP_RANGE')

        if range_h:
            m = self.RANGE_HEADER.match(range_h)
            if m:
                start = m.group(1)
                end = m.group(2)
                use_206 = True

        else:
            m = self.RANGE_ARG_RX.match(url)
            if m:
                start = m.group(2)
                end = m.group(3)
                url = url[:m.start(1)] + url[m.end(1):]
                use_206 = False

        if not start:
            return None

        start = int(start)
        self.custom_params['noredir'] = True

        if end:
            end = int(end)
        else:
            end = ''

        result = (url, start, end, use_206)
        return result

    def __repr__(self):
        varlist = vars(self)
        varstr = pprint.pformat(varlist)
        return varstr

    def _parse_extra(self):
        pass

    def extract_referrer_wburl_str(self):
        if not self.referrer:
            return None

        if not self.referrer.startswith(self.host_prefix + self.rel_prefix):
            return None

        wburl_str = self.referrer[len(self.host_prefix + self.rel_prefix):]
        return wburl_str

    def normalize_post_query(self):
        if self.method != 'POST':
            return

        if not self.wb_url:
            return

        mime = self.env.get('CONTENT_TYPE', '')
        length = self.env.get('CONTENT_LENGTH')
        stream = self.env['wsgi.input']

        buffered_stream = BytesIO()

        post_query = extract_post_query('POST', mime, length, stream,
                                        buffered_stream=buffered_stream,
                                        environ=self.env)

        if post_query:
            self.env['wsgi.input'] = buffered_stream
            self.wb_url.url = append_post_query(self.wb_url.url, post_query)


# =================================================================
class WbResponse(object):
    """
    Represnts a pywb wsgi response object.

    Holds a status_headers object and a response iter, to be
    returned to wsgi container.
    """

    def __init__(self, status_headers, value=[], **kwargs):
        self.status_headers = status_headers
        self.body = value
        self._init_derived(kwargs)

    def _init_derived(self, params):
        pass

    @staticmethod
    def text_stream(stream, content_type='text/plain; charset=utf-8', status='200 OK'):
        def encode(stream):
            for obj in stream:
                yield obj.encode('utf-8')

        if 'charset' not in content_type:
            content_type += '; charset=utf-8'

        return WbResponse.bin_stream(encode(stream), content_type, status)

    @staticmethod
    def bin_stream(stream, content_type, status='200 OK',
                   headers=None):
        def_headers = [('Content-Type', content_type)]
        if headers:
            def_headers += headers

        status_headers = StatusAndHeaders(status, def_headers)

        return WbResponse(status_headers, value=stream)

    @staticmethod
    def text_response(text, status='200 OK', content_type='text/plain; charset=utf-8'):
        status_headers = StatusAndHeaders(status,
                                          [('Content-Type', content_type),
                                           ('Content-Length', str(len(text)))])

        return WbResponse(status_headers, value=[text.encode('utf-8')])

    @staticmethod
    def redir_response(location, status='302 Redirect', headers=None):
        redir_headers = [('Location', location), ('Content-Length', '0')]
        if headers:
            redir_headers += headers

        return WbResponse(StatusAndHeaders(status, redir_headers))

    def __call__(self, env, start_response):
        start_response(self.status_headers.statusline,
                       self.status_headers.headers)

        if env['REQUEST_METHOD'] == 'HEAD':
            if hasattr(self.body, 'close'):
                self.body.close()
            return []

        return self.body

    def add_range(self, *args):
        self.status_headers.add_range(*args)
        return self

    def __repr__(self):
        return str(vars(self))


# end pywb.framework.wbrequestresponse


# begin pywb.rewrite.wburl
# =================================================================
class BaseWbUrl(object):
    QUERY = 'query'
    URL_QUERY = 'url_query'
    REPLAY = 'replay'
    LATEST_REPLAY = 'latest_replay'

    def __init__(self, url='', mod='',
                 timestamp='', end_timestamp='', type=None):
        self.url = url
        self.timestamp = timestamp
        self.end_timestamp = end_timestamp
        self.mod = mod
        self.type = type

    def is_replay(self):
        return self.is_replay_type(self.type)

    def is_latest_replay(self):
        return (self.type == BaseWbUrl.LATEST_REPLAY)

    def is_query(self):
        return self.is_query_type(self.type)

    def is_url_query(self):
        return (self.type == BaseWbUrl.URL_QUERY)

    @staticmethod
    def is_replay_type(type_):
        return (type_ == BaseWbUrl.REPLAY or
                type_ == BaseWbUrl.LATEST_REPLAY)

    @staticmethod
    def is_query_type(type_):
        return (type_ == BaseWbUrl.QUERY or
                type_ == BaseWbUrl.URL_QUERY)


# =================================================================
class WbUrl(BaseWbUrl):
    # Regexs
    # ======================
    QUERY_REGEX = re.compile('^(?:([\w\-:]+)/)?(\d*)[*-](\d*)/?(.+)$')
    REPLAY_REGEX = re.compile('^(\d*)([a-z]+_)?/{1,3}(.+)$')
    # LATEST_REPLAY_REGEX = re.compile('^\w_)')

    DEFAULT_SCHEME = 'http://'

    FIRST_PATH = re.compile('(?<![:/])[/?](?![/])')

    @staticmethod
    def percent_encode_host(url):
        """ Convert the host of uri formatted with to_uri()
        to have a %-encoded host instead of punycode host
        The rest of url should be unchanged
        """

        # only continue if punycode encoded
        if 'xn--' not in url:
            return url

        parts = urlsplit(url)
        domain = parts.netloc.encode('utf-8')
        try:
            domain = domain.decode('idna')
            if six.PY2:
                domain = domain.encode('utf-8', 'ignore')
        except:
            # likely already encoded, so use as is
            pass

        domain = quote(domain)  # , safe=r':\/')

        return urlunsplit((parts[0], domain, parts[2], parts[3], parts[4]))

    @staticmethod
    def to_uri(url):
        """ Converts a url to an ascii %-encoded form
        where:
        - scheme is ascii,
        - host is punycode,
        - and remainder is %-encoded
        Not using urlsplit to also decode partially encoded
        scheme urls
        """
        parts = WbUrl.FIRST_PATH.split(url, 1)

        sep = url[len(parts[0])] if len(parts) > 1 else None

        scheme_dom = unquote_plus(parts[0])

        if six.PY2 and isinstance(scheme_dom, six.binary_type):
            if scheme_dom == parts[0]:
                return url

            scheme_dom = scheme_dom.decode('utf-8', 'ignore')

        scheme_dom = scheme_dom.rsplit('/', 1)
        domain = scheme_dom[-1]

        try:
            domain = to_native_str(domain.encode('idna'), 'utf-8')
        except UnicodeError:
            # the url is invalid and this is probably not a domain
            pass

        if len(scheme_dom) > 1:
            url = to_native_str(scheme_dom[0], 'utf-8') + '/' + domain
        else:
            url = domain

        if len(parts) > 1:
            url += sep

            rest = parts[1]
            try:
                rest.encode('ascii')
            except UnicodeEncodeError:
                rest = quote(to_native_str(rest, 'utf-8'))

            url += rest

        return url

    # ======================

    def __init__(self, orig_url):
        super(WbUrl, self).__init__()

        if six.PY2 and isinstance(orig_url, six.text_type):
            orig_url = orig_url.encode('utf-8')
            orig_url = quote(orig_url)

        self._original_url = orig_url

        if not self._init_query(orig_url):
            if not self._init_replay(orig_url):
                raise Exception('Invalid WbUrl: ', orig_url)

        new_uri = WbUrl.to_uri(self.url)

        self._do_percent_encode = True

        self.url = new_uri

        if self.url.startswith('urn:'):
            return

        # protocol agnostic url -> http://
        # no protocol -> http://
        inx = self.url.find(':/')
        # if inx < 0:
        # check for other partially encoded variants
        #    m = self.PARTIAL_ENC_RX.match(self.url)
        #    if m:
        #        len_ = len(m.group(0))
        #        self.url = (urllib.unquote_plus(self.url[:len_]) +
        #                    self.url[len_:])
        #        inx = self.url.find(':/')

        if inx < 0:
            self.url = self.DEFAULT_SCHEME + self.url
        else:
            inx += 2
            if inx < len(self.url) and self.url[inx] != '/':
                self.url = self.url[:inx] + '/' + self.url[inx:]

    # Match query regex
    # ======================
    def _init_query(self, url):
        query = self.QUERY_REGEX.match(url)
        if not query:
            return None

        res = query.groups('')

        self.mod = res[0]
        self.timestamp = res[1]
        self.end_timestamp = res[2]
        self.url = res[3]
        if self.url.endswith('*'):
            self.type = self.URL_QUERY
            self.url = self.url[:-1]
        else:
            self.type = self.QUERY
        return True

    # Match replay regex
    # ======================
    def _init_replay(self, url):
        replay = self.REPLAY_REGEX.match(url)
        if not replay:
            if not url:
                return None

            self.timestamp = ''
            self.mod = ''
            self.url = url
            self.type = self.LATEST_REPLAY
            return True

        res = replay.groups('')

        self.timestamp = res[0]
        self.mod = res[1]
        self.url = res[2]

        if self.timestamp:
            self.type = self.REPLAY
        else:
            self.type = self.LATEST_REPLAY

        return True

    def set_replay_timestamp(self, timestamp):
        self.timestamp = timestamp
        self.type = self.REPLAY

    def deprefix_url(self, prefix):
        rex_query = '=' + re.escape(prefix) + '([0-9])*([\w]{2}_)?/?'
        self.url = re.sub(rex_query, '=', self.url)

        rex_query = '=(' + quote_plus(prefix) + '.*?)((?:https?%3A)?%2F%2F[^&]+)'
        self.url = re.sub(rex_query, '=\\2', self.url)

        return self.url

    def get_url(self, url=None):
        if url is not None:
            url = WbUrl.to_uri(url)
        else:
            url = self.url

        if self._do_percent_encode:
            url = WbUrl.percent_encode_host(url)

        return url

    # Str Representation
    # ====================
    def to_str(self, **overrides):
        type_ = overrides.get('type', self.type)
        mod = overrides.get('mod', self.mod)
        timestamp = overrides.get('timestamp', self.timestamp)
        end_timestamp = overrides.get('end_timestamp', self.end_timestamp)

        url = self.get_url(overrides.get('url', self.url))

        return self.to_wburl_str(url=url,
                                 type=type_,
                                 mod=mod,
                                 timestamp=timestamp,
                                 end_timestamp=end_timestamp)

    @staticmethod
    def to_wburl_str(url, type=BaseWbUrl.LATEST_REPLAY,
                     mod='', timestamp='', end_timestamp=''):

        if WbUrl.is_query_type(type):
            tsmod = ''
            if mod:
                tsmod += mod + "/"

            tsmod += timestamp
            tsmod += '*'
            tsmod += end_timestamp

            tsmod += "/" + url
            if type == BaseWbUrl.URL_QUERY:
                tsmod += "*"
            return tsmod
        else:
            tsmod = timestamp + mod
            if len(tsmod) > 0:
                return tsmod + "/" + url
            else:
                return url

    @property
    def is_embed(self):
        return (self.mod and
                self.mod not in ('id_', 'mp_', 'tf_', 'bn_'))

    @property
    def is_banner_only(self):
        return (self.mod == 'bn_')

    @property
    def is_url_rewrite_only(self):
        return (self.mod == 'uo_')

    @property
    def is_identity(self):
        return (self.mod == 'id_')

    def __str__(self):
        return self.to_str()

    def __repr__(self):
        return str((self.type, self.timestamp, self.mod, self.url, str(self)))


# end pywb.rewrite.wburl

# begin pywb.warc.recordloader
# =================================================================
ArcWarcRecord = collections.namedtuple('ArcWarcRecord',
                                       'format, rec_type, rec_headers, ' +
                                       'stream, status_headers, ' +
                                       'content_type, length')


# =================================================================
class ArchiveLoadFailed(WbException):
    def __init__(self, reason, filename=''):
        if filename:
            msg = filename + ': ' + str(reason)
        else:
            msg = str(reason)

        super(ArchiveLoadFailed, self).__init__(msg)

    def status(self):
        return '503 Service Unavailable'


# =================================================================
class ArcWarcRecordLoader(object):
    # Standard ARC v1.0 headers
    # TODO: support ARC v2.0 also?
    ARC_HEADERS = ["uri", "ip-address", "archive-date",
                   "content-type", "length"]

    WARC_TYPES = ['WARC/1.0', 'WARC/0.17', 'WARC/0.18']

    HTTP_TYPES = ['HTTP/1.0', 'HTTP/1.1']

    HTTP_VERBS = ['GET', 'HEAD', 'POST', 'PUT', 'DELETE', 'TRACE',
                  'OPTIONS', 'CONNECT', 'PATCH']

    NON_HTTP_RECORDS = ('warcinfo', 'arc_header', 'metadata', 'resource')

    NON_HTTP_SCHEMES = ('dns:', 'whois:', 'ntp:')
    HTTP_SCHEMES = ('http:', 'https:')

    def __init__(self, loader=None, cookie_maker=None, block_size=8192,
                 verify_http=True):
        if not loader:
            loader = BlockLoader(cookie_maker=cookie_maker)

        self.loader = loader
        self.block_size = block_size

        self.arc_parser = ARCHeadersParser(self.ARC_HEADERS)

        self.warc_parser = StatusAndHeadersParser(self.WARC_TYPES)
        self.http_parser = StatusAndHeadersParser(self.HTTP_TYPES, verify_http)

        self.http_req_parser = StatusAndHeadersParser(self.HTTP_VERBS, verify_http)

    def load(self, url, offset, length, no_record_parse=False):
        """ Load a single record from given url at offset with length
        and parse as either warc or arc record
        """
        try:
            length = int(length)
        except:
            length = -1

        stream = self.loader.load(url, int(offset), length)
        decomp_type = 'gzip'

        # Create decompressing stream
        stream = DecompressingBufferedReader(stream=stream,
                                             decomp_type=decomp_type,
                                             block_size=self.block_size)

        return self.parse_record_stream(stream, no_record_parse=no_record_parse)

    def parse_record_stream(self, stream,
                            statusline=None,
                            known_format=None,
                            no_record_parse=False):
        """ Parse file-like stream and return an ArcWarcRecord
        encapsulating the record headers, http headers (if any),
        and a stream limited to the remainder of the record.

        Pass statusline and known_format to detect_type_loader_headers()
        to faciliate parsing.
        """
        (the_format, rec_headers) = (self.
                                     _detect_type_load_headers(stream,
                                                               statusline,
                                                               known_format))

        if the_format == 'arc':
            uri = rec_headers.get_header('uri')
            length = rec_headers.get_header('length')
            content_type = rec_headers.get_header('content-type')
            sub_len = rec_headers.total_len
            if uri and uri.startswith('filedesc://'):
                rec_type = 'arc_header'
            else:
                rec_type = 'response'

        elif the_format == 'warc':
            rec_type = rec_headers.get_header('WARC-Type')
            uri = rec_headers.get_header('WARC-Target-URI')
            length = rec_headers.get_header('Content-Length')
            content_type = rec_headers.get_header('Content-Type')
            sub_len = 0

        is_err = False

        try:
            if length is not None:
                length = int(length) - sub_len
                if length < 0:
                    is_err = True

        except (ValueError, TypeError):
            is_err = True

        # err condition
        if is_err:
            length = 0

        # limit stream to the length for all valid records
        if length is not None and length >= 0:
            stream = LimitReader.wrap_stream(stream, length)

        # don't parse the http record at all
        if no_record_parse:
            status_headers = None  # StatusAndHeaders('', [])

        # if empty record (error or otherwise) set status to 204
        elif length == 0:
            if is_err:
                msg = '204 Possible Error'
            else:
                msg = '204 No Content'

            status_headers = StatusAndHeaders(msg, [])

        # response record or non-empty revisit: parse HTTP status and headers!
        elif (rec_type in ('response', 'revisit')
              and uri.startswith(self.HTTP_SCHEMES)):
            status_headers = self.http_parser.parse(stream)

        # request record: parse request
        elif ((rec_type == 'request')
              and uri.startswith(self.HTTP_SCHEMES)):
            status_headers = self.http_req_parser.parse(stream)

        # everything else: create a no-status entry, set content-type
        else:
            content_type_header = [('Content-Type', content_type)]

            if length is not None and length >= 0:
                content_type_header.append(('Content-Length', str(length)))

            status_headers = StatusAndHeaders('200 OK', content_type_header)

        return ArcWarcRecord(the_format, rec_type,
                             rec_headers, stream, status_headers,
                             content_type, length)

    def _detect_type_load_headers(self, stream,
                                  statusline=None, known_format=None):
        """ If known_format is specified ('warc' or 'arc'),
        parse only as that format.

        Otherwise, try parsing record as WARC, then try parsing as ARC.
        if neither one succeeds, we're out of luck.
        """

        if known_format != 'arc':
            # try as warc first
            try:
                rec_headers = self.warc_parser.parse(stream, statusline)
                return 'warc', rec_headers
            except StatusAndHeadersParserException as se:
                if known_format == 'warc':
                    msg = 'Invalid WARC record, first line: '
                    raise ArchiveLoadFailed(msg + str(se.statusline))

                statusline = se.statusline
                pass

        # now try as arc
        try:
            rec_headers = self.arc_parser.parse(stream, statusline)
            return 'arc', rec_headers
        except StatusAndHeadersParserException as se:
            if known_format == 'arc':
                msg = 'Invalid ARC record, first line: '
            else:
                msg = 'Unknown archive format, first line: '
            raise ArchiveLoadFailed(msg + str(se.statusline))


# =================================================================
class ARCHeadersParser(object):
    def __init__(self, headernames):
        self.headernames = headernames

    def parse(self, stream, headerline=None):
        total_read = 0

        def readline():
            return to_native_str(stream.readline())

        # if headerline passed in, use that
        if headerline is None:
            headerline = readline()
        else:
            headerline = to_native_str(headerline)

        header_len = len(headerline)

        if header_len == 0:
            raise EOFError()

        headerline = headerline.rstrip()

        headernames = self.headernames

        # if arc header, consume next two lines
        if headerline.startswith('filedesc://'):
            version = readline()  # skip version
            spec = readline()  # skip header spec, use preset one
            total_read += len(version)
            total_read += len(spec)

        parts = headerline.split(' ')

        if len(parts) != len(headernames):
            msg = 'Wrong # of headers, expected arc headers {0}, Found {1}'
            msg = msg.format(headernames, parts)
            raise StatusAndHeadersParserException(msg, parts)

        headers = []

        for name, value in zip(headernames, parts):
            headers.append((name, value))

        return StatusAndHeaders(statusline='',
                                headers=headers,
                                protocol='ARC/1.0',
                                total_len=total_read)


# end pywb.warc.recordloader

# begin pywb.warc.resolvingloader
# =================================================================
class ResolvingLoader(object):
    MISSING_REVISIT_MSG = 'Original for revisit record could not be loaded'

    def __init__(self, path_resolvers, record_loader=ArcWarcRecordLoader(), no_record_parse=False):
        self.path_resolvers = path_resolvers
        self.record_loader = record_loader
        self.no_record_parse = no_record_parse

    def __call__(self, cdx, failed_files, cdx_loader, *args, **kwargs):
        headers_record, payload_record = self.load_headers_and_payload(cdx, failed_files, cdx_loader)

        # Default handling logic when loading http status/headers

        # special case: set header to payload if old-style revisit
        # with missing header
        if not headers_record:
            headers_record = payload_record
        elif headers_record != payload_record:
            # close remainder of stream as this record only used for
            # (already parsed) headers
            headers_record.stream.close()

            # special case: check if headers record is actually empty
            # (eg empty revisit), then use headers from revisit
            if not headers_record.status_headers.headers:
                headers_record = payload_record

        if not headers_record or not payload_record:
            raise ArchiveLoadFailed('Could not load ' + str(cdx))

        # ensure status line is valid from here
        headers_record.status_headers.validate_statusline('204 No Content')

        return (headers_record.status_headers, payload_record.stream)

    def load_headers_and_payload(self, cdx, failed_files, cdx_loader):
        """
        Resolve headers and payload for a given capture
        In the simple case, headers and payload are in the same record.
        In the case of revisit records, the payload and headers may be in
        different records.

        If the original has already been found, lookup original using
        orig. fields in cdx dict.
        Otherwise, call _load_different_url_payload() to get cdx index
        from a different url to find the original record.
        """
        has_curr = (cdx['filename'] != '-')
        # has_orig = (cdx.get('orig.filename', '-') != '-')
        orig_f = cdx.get('orig.filename')
        has_orig = orig_f and orig_f != '-'

        # load headers record from cdx['filename'] unless it is '-' (rare)
        headers_record = None
        if has_curr:
            headers_record = self._resolve_path_load(cdx, False, failed_files)

        # two index lookups
        # Case 1: if mimetype is still warc/revisit
        if cdx.get('mime') == 'warc/revisit' and headers_record:
            payload_record = self._load_different_url_payload(cdx,
                                                              headers_record,
                                                              failed_files,
                                                              cdx_loader)

        # single lookup cases
        # case 2: non-revisit
        elif (has_curr and not has_orig):
            payload_record = headers_record

        # case 3: identical url revisit, load payload from orig.filename
        elif (has_orig):
            payload_record = self._resolve_path_load(cdx, True, failed_files)

        return headers_record, payload_record

    def _resolve_path_load(self, cdx, is_original, failed_files):
        """
        Load specific record based on filename, offset and length
        fields in the cdx.
        If original=True, use the orig.* fields for the cdx

        Resolve the filename to full path using specified path resolvers

        If failed_files list provided, keep track of failed resolve attempts
        """

        if is_original:
            (filename, offset, length) = (cdx['orig.filename'],
                                          cdx['orig.offset'],
                                          cdx['orig.length'])
        else:
            (filename, offset, length) = (cdx['filename'],
                                          cdx['offset'],
                                          cdx.get('length', '-'))

        # optimization: if same file already failed this request,
        # don't try again
        if failed_files is not None and filename in failed_files:
            raise ArchiveLoadFailed('Skipping Already Failed', filename)

        any_found = False
        last_exc = None
        last_traceback = None
        for resolver in self.path_resolvers:
            possible_paths = resolver(filename, cdx)

            if not possible_paths:
                continue

            if isinstance(possible_paths, six.string_types):
                possible_paths = [possible_paths]

            for path in possible_paths:
                any_found = True
                try:
                    return (self.record_loader.
                            load(path, offset, length,
                                 no_record_parse=self.no_record_parse))

                except Exception as ue:
                    last_exc = ue
                    import sys
                    last_traceback = sys.exc_info()[2]

        # Unsuccessful if reached here
        if failed_files is not None:
            failed_files.append(filename)

        if last_exc:
            # msg = str(last_exc.__class__.__name__)
            msg = str(last_exc)
        else:
            msg = 'Archive File Not Found'

        # raise ArchiveLoadFailed(msg, filename), None, last_traceback
        six.reraise(ArchiveLoadFailed, ArchiveLoadFailed(msg, filename), last_traceback)

    def _load_different_url_payload(self, cdx, headers_record,
                                    failed_files, cdx_loader):
        """
        Handle the case where a duplicate of a capture with same digest
        exists at a different url.

        If a cdx_server is provided, a query is made for matching
        url, timestamp and digest.

        Raise exception if no matches found.
        """

        ref_target_uri = (headers_record.rec_headers.
                          get_header('WARC-Refers-To-Target-URI'))

        target_uri = headers_record.rec_headers.get_header('WARC-Target-URI')

        # if no target uri, no way to find the original
        if not ref_target_uri:
            raise ArchiveLoadFailed(self.MISSING_REVISIT_MSG)

        ref_target_date = (headers_record.rec_headers.
                           get_header('WARC-Refers-To-Date'))

        if not ref_target_date:
            ref_target_date = cdx['timestamp']
        else:
            ref_target_date = iso_date_to_timestamp(ref_target_date)

        digest = cdx.get('digest', '-')

        try:
            orig_cdx_lines = self.load_cdx_for_dupe(ref_target_uri,
                                                    ref_target_date,
                                                    digest,
                                                    cdx_loader)
        except NotFoundException:
            raise ArchiveLoadFailed(self.MISSING_REVISIT_MSG)

        for orig_cdx in orig_cdx_lines:
            try:
                payload_record = self._resolve_path_load(orig_cdx, False,
                                                         failed_files)
                return payload_record

            except ArchiveLoadFailed as e:
                pass

        raise ArchiveLoadFailed(self.MISSING_REVISIT_MSG)

    def load_cdx_for_dupe(self, url, timestamp, digest, cdx_loader):
        """
        If a cdx_server is available, return response from server,
        otherwise empty list
        """
        if not cdx_loader:
            return iter([])

        filters = []

        filters.append('!mime:warc/revisit')

        if digest and digest != '-':
            filters.append('digest:' + digest)

        params = dict(url=url,
                      closest=timestamp,
                      filter=filters)

        return cdx_loader(params)


# end  pywb.warc.resolvingloader


# begin pywb.warc.pathresolvers
# =================================================================
# PrefixResolver - convert cdx file entry to url with prefix
# if url contains specified string
# =================================================================
class PrefixResolver(object):
    def __init__(self, prefix, contains):
        self.prefix = prefix
        self.contains = contains if contains else ''

    def __call__(self, filename, cdx=None):
        # use os path seperator
        filename = filename.replace('/', os.path.sep)
        return [self.prefix + filename] if (self.contains in filename) else []

    def __repr__(self):
        if self.contains:
            return ("PrefixResolver('{0}', contains = '{1}')"
                    .format(self.prefix, self.contains))
        else:
            return "PrefixResolver('{0}')".format(self.prefix)


# =================================================================
class RedisResolver(object):
    def __init__(self, redis_url, key_prefix=None):
        self.redis_url = redis_url
        self.key_prefix = key_prefix if key_prefix else 'w:'
        self.redis = redis.StrictRedis.from_url(redis_url)

    def __call__(self, filename, cdx=None):
        redis_val = self.redis.hget(self.key_prefix + filename, 'path')
        return [to_native_str(redis_val, 'utf-8')] if redis_val else []

    def __repr__(self):
        return "RedisResolver('{0}')".format(self.redis_url)


# =================================================================
class PathIndexResolver(object):
    def __init__(self, pathindex_file):
        self.pathindex_file = pathindex_file

    def __call__(self, filename, cdx=None):
        with open(self.pathindex_file, 'rb') as reader:
            result = iter_exact(reader, filename.encode('utf-8'), b'\t')

            for pathline in result:
                paths = pathline.split(b'\t')[1:]
                for path in paths:
                    yield to_native_str(path, 'utf-8')

    def __repr__(self):  # pragma: no cover
        return "PathIndexResolver('{0}')".format(self.pathindex_file)


# =================================================================
class PathResolverMapper(object):
    def make_best_resolver(self, param):
        if isinstance(param, list):
            path = param[0]
            arg = param[1]
        else:
            path = param
            arg = None

        url_parts = urlsplit(path)

        if url_parts.scheme == 'redis':
            logging.debug('Adding Redis Index: ' + path)
            return RedisResolver(path, arg)

        if url_parts.scheme == 'file':
            path = url_parts.path
            path = url2pathname(path)

        if os.path.isfile(path):
            logging.debug('Adding Path Index: ' + path)
            return PathIndexResolver(path)

        # non-file paths always treated as prefix for now
        else:
            logging.debug('Adding Archive Path Source: ' + path)
            return PrefixResolver(path, arg)

    def __call__(self, paths):
        if isinstance(paths, list) or isinstance(paths, set):
            return list(map(self.make_best_resolver, paths))
        else:
            return [self.make_best_resolver(paths)]


# end pywb.warc.pathresolvers

# begin pywb.warc.archiveiterator
#=================================================================
class ArchiveIterator(object):
    """ Iterate over records in WARC and ARC files, both gzip chunk
    compressed and uncompressed

    The indexer will automatically detect format, and decompress
    if necessary.

    """

    GZIP_ERR_MSG = """
    ERROR: Non-chunked gzip file detected, gzip block continues
    beyond single record.

    This file is probably not a multi-chunk gzip but a single gzip file.

    To allow seek, a gzipped {1} must have each record compressed into
    a single gzip chunk and concatenated together.

    This file is likely still valid and you can use it by decompressing it:

    gunzip myfile.{0}.gz

    You can then also use the 'warc2warc' tool from the 'warc-tools'
    package which will create a properly chunked gzip file:

    warc2warc -Z myfile.{0} > myfile.{0}.gz
"""

    INC_RECORD = """\
    WARNING: Record not followed by newline, perhaps Content-Length is invalid
    Offset: {0}
    Remainder: {1}
"""


    def __init__(self, fileobj, no_record_parse=False,
                 verify_http=False):
        self.fh = fileobj

        self.loader = ArcWarcRecordLoader(verify_http=verify_http)
        self.reader = None

        self.offset = 0
        self.known_format = None

        self.member_info = None
        self.no_record_parse = no_record_parse

    def __call__(self, block_size=16384):
        """ iterate over each record
        """

        decomp_type = 'gzip'

        self.reader = DecompressingBufferedReader(self.fh,
                                                  block_size=block_size)
        self.offset = self.fh.tell()

        self.next_line = None

        raise_invalid_gzip = False
        empty_record = False
        record = None

        while True:
            try:
                curr_offset = self.fh.tell()
                record = self._next_record(self.next_line)
                if raise_invalid_gzip:
                    self._raise_invalid_gzip_err()

                yield record

            except EOFError:
                empty_record = True

            if record:
                self.read_to_end(record)

            if self.reader.decompressor:
                # if another gzip member, continue
                if self.reader.read_next_member():
                    continue

                # if empty record, then we're done
                elif empty_record:
                    break

                # otherwise, probably a gzip
                # containing multiple non-chunked records
                # raise this as an error
                else:
                    raise_invalid_gzip = True

            # non-gzip, so we're done
            elif empty_record:
                break

    def _raise_invalid_gzip_err(self):
        """ A gzip file with multiple ARC/WARC records, non-chunked
        has been detected. This is not valid for replay, so notify user
        """
        frmt = 'warc/arc'
        if self.known_format:
            frmt = self.known_format

        frmt_up = frmt.upper()

        msg = self.GZIP_ERR_MSG.format(frmt, frmt_up)
        raise Exception(msg)

    def _consume_blanklines(self):
        """ Consume blank lines that are between records
        - For warcs, there are usually 2
        - For arcs, may be 1 or 0
        - For block gzipped files, these are at end of each gzip envelope
          and are included in record length which is the full gzip envelope
        - For uncompressed, they are between records and so are NOT part of
          the record length

          count empty_size so that it can be substracted from
          the record length for uncompressed

          if first line read is not blank, likely error in WARC/ARC,
          display a warning
        """
        empty_size = 0
        first_line = True

        while True:
            line = self.reader.readline()
            if len(line) == 0:
                return None, empty_size

            stripped = line.rstrip()

            if len(stripped) == 0 or first_line:
                empty_size += len(line)

                if len(stripped) != 0:
                    # if first line is not blank,
                    # likely content-length was invalid, display warning
                    err_offset = self.fh.tell() - self.reader.rem_length() - empty_size
                    sys.stderr.write(self.INC_RECORD.format(err_offset, line))

                first_line = False
                continue

            return line, empty_size

    def read_to_end(self, record, payload_callback=None):
        """ Read remainder of the stream
        If a digester is included, update it
        with the data read
        """

        # already at end of this record, don't read until it is consumed
        if self.member_info:
            return None

        num = 0
        curr_offset = self.offset

        while True:
            b = record.stream.read(8192)
            if not b:
                break
            num += len(b)
            if payload_callback:
                payload_callback(b)

        """
        - For compressed files, blank lines are consumed
          since they are part of record length
        - For uncompressed files, blank lines are read later,
          and not included in the record length
        """
        #if self.reader.decompressor:
        self.next_line, empty_size = self._consume_blanklines()

        self.offset = self.fh.tell() - self.reader.rem_length()
        #if self.offset < 0:
        #    raise Exception('Not Gzipped Properly')

        if self.next_line:
            self.offset -= len(self.next_line)

        length = self.offset - curr_offset

        if not self.reader.decompressor:
            length -= empty_size

        self.member_info = (curr_offset, length)
        #return self.member_info
        #return next_line

    def _next_record(self, next_line):
        """ Use loader to parse the record from the reader stream
        Supporting warc and arc records
        """
        record = self.loader.parse_record_stream(self.reader,
                                                 next_line,
                                                 self.known_format,
                                                 self.no_record_parse)

        self.member_info = None

        # Track known format for faster parsing of other records
        self.known_format = record.format

        return record


#=================================================================
class ArchiveIndexEntryMixin(object):
    MIME_RE = re.compile('[; ]')

    def __init__(self):
        super(ArchiveIndexEntryMixin, self).__init__()
        self.reset_entry()

    def reset_entry(self):
        self['urlkey'] = ''
        self['metadata'] = ''
        self.buffer = None
        self.record = None


    def extract_mime(self, mime, def_mime='unk'):
        """ Utility function to extract mimetype only
        from a full content type, removing charset settings
        """
        self['mime'] = def_mime
        if mime:
            self['mime'] = self.MIME_RE.split(mime, 1)[0]
            self['_content_type'] = mime

    def extract_status(self, status_headers):
        """ Extract status code only from status line
        """
        self['status'] = status_headers.get_statuscode()
        if not self['status']:
            self['status'] = '-'
        elif self['status'] == '204' and 'Error' in status_headers.statusline:
            self['status'] = '-'

    def set_rec_info(self, offset, length):
        self['length'] = str(length)
        self['offset'] = str(offset)

    def merge_request_data(self, other, options):
        surt_ordered = options.get('surt_ordered', True)

        if other.record.rec_type != 'request':
            return False

        # two requests, not correct
        if self.record.rec_type == 'request':
            return False

        # merge POST/PUT body query
        post_query = other.get('_post_query')
        if post_query:
            url = append_post_query(self['url'], post_query)
            self['urlkey'] = canonicalize(url, surt_ordered)
            other['urlkey'] = self['urlkey']

        referer = other.record.status_headers.get_header('referer')
        if referer:
            self['_referer'] = referer

        return True


#=================================================================
class DefaultRecordParser(object):
    def __init__(self, **options):
        self.options = options
        self.entry_cache = {}
        self.digester = None
        self.buff = None

    def _create_index_entry(self, rec_type):
        try:
            entry = self.entry_cache[rec_type]
            entry.reset_entry()
        except:
            if self.options.get('cdxj'):
                entry = OrderedArchiveIndexEntry()
            else:
                entry = ArchiveIndexEntry()

            # don't reuse when using append post
            # entry may be cached
            if not self.options.get('append_post'):
                self.entry_cache[rec_type] = entry

        return entry

    def begin_payload(self, compute_digest, entry):
        if compute_digest:
            self.digester = hashlib.sha1()
        else:
            self.digester = None

        self.entry = entry
        entry.buffer = self.create_payload_buffer(entry)

    def handle_payload(self, buff):
        if self.digester:
            self.digester.update(buff)

        if self.entry and self.entry.buffer:
            self.entry.buffer.write(buff)

    def end_payload(self, entry):
        if self.digester:
            entry['digest'] = base64.b32encode(self.digester.digest()).decode('ascii')

        self.entry = None

    def create_payload_buffer(self, entry):
        return None

    def create_record_iter(self, raw_iter):
        append_post = self.options.get('append_post')
        include_all = self.options.get('include_all')
        block_size = self.options.get('block_size', 16384)
        surt_ordered = self.options.get('surt_ordered', True)
        minimal = self.options.get('minimal')

        if append_post and minimal:
            raise Exception('Sorry, minimal index option and ' +
                            'append POST options can not be used together')

        for record in raw_iter(block_size):
            entry = None

            if not include_all and not minimal and (record.status_headers.get_statuscode() == '-'):
                continue

            if record.format == 'warc':
                if (record.rec_type in ('request', 'warcinfo') and
                     not include_all and
                     not append_post):
                    continue

                elif (not include_all and
                      record.content_type == 'application/warc-fields'):
                    continue

                entry = self.parse_warc_record(record)
            elif record.format == 'arc':
                entry = self.parse_arc_record(record)

            if not entry:
                continue

            if entry.get('url') and not entry.get('urlkey'):
                entry['urlkey'] = canonicalize(entry['url'], surt_ordered)

            compute_digest = False

            if (entry.get('digest', '-') == '-' and
                record.rec_type not in ('revisit', 'request', 'warcinfo')):

                compute_digest = True

            elif not minimal and record.rec_type == 'request' and append_post:
                method = record.status_headers.protocol
                len_ = record.status_headers.get_header('Content-Length')

                post_query = extract_post_query(method,
                                                entry.get('_content_type'),
                                                len_,
                                                record.stream)

                entry['_post_query'] = post_query

            entry.record = record

            self.begin_payload(compute_digest, entry)
            raw_iter.read_to_end(record, self.handle_payload)

            entry.set_rec_info(*raw_iter.member_info)
            self.end_payload(entry)

            yield entry

    def join_request_records(self, entry_iter):
        prev_entry = None

        for entry in entry_iter:
            if not prev_entry:
                prev_entry = entry
                continue

            # check for url match
            if (entry['url'] != prev_entry['url']):
                pass

            # check for concurrency also
            elif (entry.record.rec_headers.get_header('WARC-Concurrent-To') !=
                  prev_entry.record.rec_headers.get_header('WARC-Record-ID')):
                pass

            elif (entry.merge_request_data(prev_entry, self.options) or
                  prev_entry.merge_request_data(entry, self.options)):
                yield prev_entry
                yield entry
                prev_entry = None
                continue

            yield prev_entry
            prev_entry = entry

        if prev_entry:
            yield prev_entry


    #=================================================================
    def parse_warc_record(self, record):
        """ Parse warc record
        """

        entry = self._create_index_entry(record.rec_type)

        if record.rec_type == 'warcinfo':
            entry['url'] = record.rec_headers.get_header('WARC-Filename')
            entry['urlkey'] = entry['url']
            entry['_warcinfo'] = record.stream.read(record.length)
            return entry

        entry['url'] = record.rec_headers.get_header('WARC-Target-Uri')

        # timestamp
        entry['timestamp'] = iso_date_to_timestamp(record.rec_headers.
                                                   get_header('WARC-Date'))

        # mime
        if record.rec_type == 'revisit':
            entry['mime'] = 'warc/revisit'
        elif self.options.get('minimal'):
            entry['mime'] = '-'
        else:
            def_mime = '-' if record.rec_type == 'request' else 'unk'
            entry.extract_mime(record.status_headers.
                               get_header('Content-Type'),
                               def_mime)

        # status -- only for response records (by convention):
        if record.rec_type == 'response' and not self.options.get('minimal'):
            entry.extract_status(record.status_headers)
        else:
            entry['status'] = '-'

        # digest
        digest = record.rec_headers.get_header('WARC-Payload-Digest')
        entry['digest'] = digest
        if digest and digest.startswith('sha1:'):
            entry['digest'] = digest[len('sha1:'):]

        elif not entry.get('digest'):
            entry['digest'] = '-'

        # optional json metadata, if present
        metadata = record.rec_headers.get_header('WARC-Json-Metadata')
        if metadata:
            entry['metadata'] = metadata

        return entry


    #=================================================================
    def parse_arc_record(self, record):
        """ Parse arc record
        """
        if record.rec_type == 'arc_header':
            return None

        url = record.rec_headers.get_header('uri')
        url = url.replace('\r', '%0D')
        url = url.replace('\n', '%0A')
        # replace formfeed
        url = url.replace('\x0c', '%0C')
        # replace nulls
        url = url.replace('\x00', '%00')

        entry = self._create_index_entry(record.rec_type)
        entry['url'] = url

        # timestamp
        entry['timestamp'] = record.rec_headers.get_header('archive-date')
        if len(entry['timestamp']) > 14:
            entry['timestamp'] = entry['timestamp'][:14]

        if not self.options.get('minimal'):
            # mime
            entry.extract_mime(record.rec_headers.get_header('content-type'))

            # status
            entry.extract_status(record.status_headers)

        # digest
        entry['digest'] = '-'

        return entry

    def __call__(self, fh):
        aiter = ArchiveIterator(fh, self.options.get('minimal', False),
                                    self.options.get('verify_http', False))

        entry_iter = self.create_record_iter(aiter)

        if self.options.get('append_post'):
            entry_iter = self.join_request_records(entry_iter)

        for entry in entry_iter:
            if (entry.record.rec_type in ('request', 'warcinfo') and
                 not self.options.get('include_all')):
                continue

            yield entry

    def open(self, filename):
        with open(filename, 'rb') as fh:
            for entry in self(fh):
                yield entry

class ArchiveIndexEntry(ArchiveIndexEntryMixin, dict):
    pass

class OrderedArchiveIndexEntry(ArchiveIndexEntryMixin, OrderedDict):
    pass

# end pywb.warc.archiveiterator

# begin pywb.warc.cdxIndexer
#=================================================================
class BaseCDXWriter(object):
    def __init__(self, out):
        self.out = codecs.getwriter('utf-8')(out)
        #self.out = out

    def __enter__(self):
        self._write_header()
        return self

    def write(self, entry, filename):
        if not entry.get('url') or not entry.get('urlkey'):
            return

        if entry.record.rec_type == 'warcinfo':
            return

        self.write_cdx_line(self.out, entry, filename)

    def __exit__(self, *args):
        return False


#=================================================================
class CDXJ(object):
    def _write_header(self):
        pass

    def write_cdx_line(self, out, entry, filename):
        out.write(entry['urlkey'])
        out.write(' ')
        out.write(entry['timestamp'])
        out.write(' ')

        outdict = OrderedDict()

        for n, v in six.iteritems(entry):
            if n in ('urlkey', 'timestamp'):
                continue

            if n.startswith('_'):
                continue

            if not v or v == '-':
                continue

            outdict[n] = v

        outdict['filename'] = filename
        out.write(json_encode(outdict))
        out.write('\n')


#=================================================================
class CDX09(object):
    def _write_header(self):
        self.out.write(' CDX N b a m s k r V g\n')

    def write_cdx_line(self, out, entry, filename):
        out.write(entry['urlkey'])
        out.write(' ')
        out.write(entry['timestamp'])
        out.write(' ')
        out.write(entry['url'])
        out.write(' ')
        out.write(entry['mime'])
        out.write(' ')
        out.write(entry['status'])
        out.write(' ')
        out.write(entry['digest'])
        out.write(' - ')
        out.write(entry['offset'])
        out.write(' ')
        out.write(filename)
        out.write('\n')


#=================================================================
class CDX11(object):
    def _write_header(self):
        self.out.write(' CDX N b a m s k r M S V g\n')

    def write_cdx_line(self, out, entry, filename):
        out.write(entry['urlkey'])
        out.write(' ')
        out.write(entry['timestamp'])
        out.write(' ')
        out.write(entry['url'])
        out.write(' ')
        out.write(entry['mime'])
        out.write(' ')
        out.write(entry['status'])
        out.write(' ')
        out.write(entry['digest'])
        out.write(' - - ')
        out.write(entry['length'])
        out.write(' ')
        out.write(entry['offset'])
        out.write(' ')
        out.write(filename)
        out.write('\n')


#=================================================================
class SortedCDXWriter(BaseCDXWriter):
    def __enter__(self):
        self.sortlist = []
        res = super(SortedCDXWriter, self).__enter__()
        self.actual_out = self.out
        return res

    def write(self, entry, filename):
        self.out = StringIO()
        super(SortedCDXWriter, self).write(entry, filename)
        line = self.out.getvalue()
        if line:
            insort(self.sortlist, line)

    def __exit__(self, *args):
        self.actual_out.write(''.join(self.sortlist))
        return False


#=================================================================
ALLOWED_EXT = ('.arc', '.arc.gz', '.warc', '.warc.gz')


#=================================================================
def _resolve_rel_path(path, rel_root):
    path = os.path.relpath(path, rel_root)
    if os.path.sep != '/':  #pragma: no cover
        path = path.replace(os.path.sep, '/')
    return path


#=================================================================
def iter_file_or_dir(inputs, recursive=True, rel_root=None):
    for input_ in inputs:
        if not os.path.isdir(input_):
            if not rel_root:
                filename = os.path.basename(input_)
            else:
                filename = _resolve_rel_path(input_, rel_root)

            yield input_, filename

        elif not recursive:
            for filename in os.listdir(input_):
                if filename.endswith(ALLOWED_EXT):
                    full_path = os.path.join(input_, filename)
                    if rel_root:
                        filename = _resolve_rel_path(full_path, rel_root)
                    yield full_path, filename

        else:
            for root, dirs, files in os.walk(input_):
                for filename in files:
                    if filename.endswith(ALLOWED_EXT):
                        full_path = os.path.join(root, filename)
                        if not rel_root:
                            rel_root = input_
                        rel_path = _resolve_rel_path(full_path, rel_root)
                        yield full_path, rel_path


#=================================================================
def remove_ext(filename):
    for ext in ALLOWED_EXT:
        if filename.endswith(ext):
            filename = filename[:-len(ext)]
            break

    return filename


#=================================================================
def cdx_filename(filename):
    return remove_ext(filename) + '.cdx'


#=================================================================
def get_cdx_writer_cls(options):
    if options.get('minimal'):
        options['cdxj'] = True

    writer_cls = options.get('writer_cls')
    if writer_cls:
        if not options.get('writer_add_mixin'):
            return writer_cls
    elif options.get('sort'):
        writer_cls = SortedCDXWriter
    else:
        writer_cls = BaseCDXWriter

    if options.get('cdxj'):
        format_mixin = CDXJ
    elif options.get('cdx09'):
        format_mixin = CDX09
    else:
        format_mixin = CDX11

    class CDXWriter(writer_cls, format_mixin):
        pass

    return CDXWriter


#=================================================================
def write_multi_cdx_index(output, inputs, **options):
    recurse = options.get('recurse', False)
    rel_root = options.get('rel_root')

    # write one cdx per dir
    if output != '-' and os.path.isdir(output):
        for fullpath, filename in iter_file_or_dir(inputs,
                                                   recurse,
                                                   rel_root):
            outpath = cdx_filename(filename)
            outpath = os.path.join(output, outpath)

            with open(outpath, 'wb') as outfile:
                with open(fullpath, 'rb') as infile:
                    writer = write_cdx_index(outfile, infile, filename,
                                             **options)

        return writer

    # write to one cdx file
    else:
        if output == '-':
            if hasattr(sys.stdout, 'buffer'):
                outfile = sys.stdout.buffer
            else:
                outfile = sys.stdout
        else:
            outfile = open(output, 'wb')

        writer_cls = get_cdx_writer_cls(options)
        record_iter = DefaultRecordParser(**options)

        with writer_cls(outfile) as writer:
            for fullpath, filename in iter_file_or_dir(inputs,
                                                       recurse,
                                                       rel_root):
                with open(fullpath, 'rb') as infile:
                    entry_iter = record_iter(infile)

                    for entry in entry_iter:
                        writer.write(entry, filename)

        return writer


#=================================================================
def write_cdx_index(outfile, infile, filename, **options):
    #filename = filename.encode(sys.getfilesystemencoding())

    writer_cls = get_cdx_writer_cls(options)

    with writer_cls(outfile) as writer:
        entry_iter = DefaultRecordParser(**options)(infile)

        for entry in entry_iter:
            writer.write(entry, filename)

    return writer


# end pywb.warc.cdxIndexer

# begin pywb.cdx.cdxobject
# =================================================================
class CDXObject(OrderedDict):
    """
    dictionary object representing parsed CDX line.
    """
    CDX_FORMATS = [
        # Public CDX Format
        [URLKEY, TIMESTAMP, ORIGINAL, MIMETYPE, STATUSCODE,
         DIGEST, LENGTH],

        # CDX 11 Format
        [URLKEY, TIMESTAMP, ORIGINAL, MIMETYPE, STATUSCODE,
         DIGEST, REDIRECT, ROBOTFLAGS, LENGTH, OFFSET, FILENAME],

        # CDX 10 Format
        [URLKEY, TIMESTAMP, ORIGINAL, MIMETYPE, STATUSCODE,
         DIGEST, REDIRECT, ROBOTFLAGS, OFFSET, FILENAME],

        # CDX 9 Format
        [URLKEY, TIMESTAMP, ORIGINAL, MIMETYPE, STATUSCODE,
         DIGEST, REDIRECT, OFFSET, FILENAME],

        # CDX 11 Format + 3 revisit resolve fields
        [URLKEY, TIMESTAMP, ORIGINAL, MIMETYPE, STATUSCODE,
         DIGEST, REDIRECT, ROBOTFLAGS, LENGTH, OFFSET, FILENAME,
         ORIG_LENGTH, ORIG_OFFSET, ORIG_FILENAME],

        # CDX 10 Format + 3 revisit resolve fields
        [URLKEY, TIMESTAMP, ORIGINAL, MIMETYPE, STATUSCODE,
         DIGEST, REDIRECT, ROBOTFLAGS, OFFSET, FILENAME,
         ORIG_LENGTH, ORIG_OFFSET, ORIG_FILENAME],

        # CDX 9 Format + 3 revisit resolve fields
        [URLKEY, TIMESTAMP, ORIGINAL, MIMETYPE, STATUSCODE,
         DIGEST, REDIRECT, OFFSET, FILENAME,
         ORIG_LENGTH, ORIG_OFFSET, ORIG_FILENAME],
    ]

    CDX_ALT_FIELDS = {
        'u': ORIGINAL,
        'original': ORIGINAL,

        'statuscode': STATUSCODE,
        's': STATUSCODE,

        'mimetype': MIMETYPE,
        'm': MIMETYPE,

        'l': LENGTH,
        's': LENGTH,

        'o': OFFSET,

        'd': DIGEST,

        't': TIMESTAMP,

        'k': URLKEY,

        'f': FILENAME
    }

    def __init__(self, cdxline=b''):
        OrderedDict.__init__(self)

        cdxline = cdxline.rstrip()
        self._from_json = False
        self._cached_json = None

        # Allows for filling the fields later or in a custom way
        if not cdxline:
            self.cdxline = cdxline
            return

        fields = cdxline.split(b' ', 2)
        # Check for CDX JSON
        if fields[-1].startswith(b'{'):
            self[URLKEY] = to_native_str(fields[0], 'utf-8')
            self[TIMESTAMP] = to_native_str(fields[1], 'utf-8')
            json_fields = json_decode(to_native_str(fields[-1], 'utf-8'))
            for n, v in six.iteritems(json_fields):
                n = to_native_str(n, 'utf-8')
                n = self.CDX_ALT_FIELDS.get(n, n)

                if n == 'url':
                    try:
                        v.encode('ascii')
                    except UnicodeEncodeError:
                        v = quote(v.encode('utf-8'), safe=':/')

                if n != 'filename':
                    v = to_native_str(v, 'utf-8')

                self[n] = v

            self.cdxline = cdxline
            self._from_json = True
            return

        more_fields = fields.pop().split(b' ')
        fields.extend(more_fields)

        cdxformat = None
        for i in self.CDX_FORMATS:
            if len(i) == len(fields):
                cdxformat = i

        if not cdxformat:
            msg = 'unknown {0}-field cdx format'.format(len(fields))
            raise CDXException(msg)

        for header, field in zip(cdxformat, fields):
            self[header] = to_native_str(field, 'utf-8')

        self.cdxline = cdxline

    def __setitem__(self, key, value):
        OrderedDict.__setitem__(self, key, value)

        # force regen on next __str__ call
        self.cdxline = None

        # force regen on next to_json() call
        self._cached_json = None

    def is_revisit(self):
        """return ``True`` if this record is a revisit record."""
        return (self.get(MIMETYPE) == 'warc/revisit' or
                self.get(FILENAME) == '-')

    def to_text(self, fields=None):
        """
        return plaintext CDX record (includes newline).
        if ``fields`` is ``None``, output will have all fields
        in the order they are stored.

        :param fields: list of field names to output.
        """
        if fields is None:
            return str(self) + '\n'

        try:
            result = ' '.join(str(self[x]) for x in fields) + '\n'
        except KeyError as ke:
            msg = 'Invalid field "{0}" found in fields= argument'
            msg = msg.format(str(ke))
            raise CDXException(msg)

        return result

    def to_json(self, fields=None):
        return self.conv_to_json(self, fields)

    @staticmethod
    def conv_to_json(obj, fields=None):
        """
        return cdx as json dictionary string
        if ``fields`` is ``None``, output will include all fields
        in order stored, otherwise only specified fields will be
        included

        :param fields: list of field names to output
        """
        if fields is None:
            return json_encode(OrderedDict(((x, obj[x]) for x in obj if not x.startswith('_')))) + '\n'

        result = json_encode(OrderedDict([(x, obj[x]) for x in fields if x in obj])) + '\n'

        return result

    def __str__(self):
        if self.cdxline:
            return to_native_str(self.cdxline, 'utf-8')

        if not self._from_json:
            return ' '.join(str(val) for val in six.itervalues(self))
        else:
            return json_encode(self)

    def to_cdxj(self, fields=None):
        prefix = self['urlkey'] + ' ' + self['timestamp'] + ' '
        dupe = OrderedDict(list(self.items())[2:])
        return prefix + self.conv_to_json(dupe, fields)

    def __lt__(self, other):
        if not self._cached_json:
            self._cached_json = self.to_json()

        if not other._cached_json:
            other._cached_json = other.to_json()

        res = self._cached_json < other._cached_json
        return res

    def __le__(self, other):
        if not self._cached_json:
            self._cached_json = self.to_json()

        if not other._cached_json:
            other._cached_json = other.to_json()

        res = (self._cached_json <= other._cached_json)
        return res


# =================================================================
class IDXObject(OrderedDict):
    FORMAT = ['urlkey', 'part', 'offset', 'length', 'lineno']
    NUM_REQ_FIELDS = len(FORMAT) - 1  # lineno is an optional field

    def __init__(self, idxline):
        OrderedDict.__init__(self)

        idxline = idxline.rstrip()
        fields = idxline.split(b'\t')

        if len(fields) < self.NUM_REQ_FIELDS:
            msg = 'invalid idx format: {0} fields found, {1} required'
            raise CDXException(msg.format(len(fields), self.NUM_REQ_FIELDS))

        for header, field in zip(self.FORMAT, fields):
            self[header] = to_native_str(field, 'utf-8')

        self['offset'] = int(self['offset'])
        self['length'] = int(self['length'])
        lineno = self.get('lineno')
        if lineno:
            self['lineno'] = int(lineno)

        self.idxline = idxline

    def to_text(self, fields=None):
        """
        return plaintext IDX record (including newline).

        :param fields: list of field names to output (currently ignored)
        """
        return str(self) + '\n'

    def to_json(self, fields=None):
        return json_encode(self) + '\n'

    def __str__(self):
        return to_native_str(self.idxline, 'utf-8')


# end pywb.cdx.cdxobject

# begin pywb.cdx.cdxops
# =================================================================
def cdx_load(sources, query, process=True):
    """
    merge text CDX lines from sources, return an iterator for
    filtered and access-checked sequence of CDX objects.

    :param sources: iterable for text CDX sources.
    :param process: bool, perform processing sorting/filtering/grouping ops
    """
    cdx_iter = create_merged_cdx_gen(sources, query)

    # page count is a special case, no further processing
    if query.page_count:
        return cdx_iter

    cdx_iter = make_obj_iter(cdx_iter, query)

    if process and not query.secondary_index_only:
        cdx_iter = process_cdx(cdx_iter, query)

    custom_ops = query.custom_ops
    for op in custom_ops:
        cdx_iter = op(cdx_iter, query)

    if query.output == 'text':
        cdx_iter = cdx_to_text(cdx_iter, query.fields)
    elif query.output == 'json':
        cdx_iter = cdx_to_json(cdx_iter, query.fields)

    return cdx_iter


# =================================================================
def cdx_to_text(cdx_iter, fields):
    for cdx in cdx_iter:
        yield cdx.to_text(fields)


# =================================================================
def cdx_to_json(cdx_iter, fields):
    for cdx in cdx_iter:
        yield cdx.to_json(fields)


# =================================================================
def process_cdx(cdx_iter, query):
    if query.resolve_revisits:
        cdx_iter = cdx_resolve_revisits(cdx_iter)

    filters = query.filters
    if filters:
        cdx_iter = cdx_filter(cdx_iter, filters)

    if query.from_ts or query.to_ts:
        cdx_iter = cdx_clamp(cdx_iter, query.from_ts, query.to_ts)

    collapse_time = query.collapse_time
    if collapse_time:
        cdx_iter = cdx_collapse_time_status(cdx_iter, collapse_time)

    closest = query.closest
    reverse = query.reverse
    limit = query.limit

    if closest:
        cdx_iter = cdx_sort_closest(closest, cdx_iter, limit)

    elif reverse:
        cdx_iter = cdx_reverse(cdx_iter, limit)

    elif limit:
        cdx_iter = cdx_limit(cdx_iter, limit)

    return cdx_iter


# =================================================================
def create_merged_cdx_gen(sources, query):
    """
    create a generator which loads and merges cdx streams
    ensures cdxs are lazy loaded
    """
    # Optimize: no need to merge if just one input
    if len(sources) == 1:
        cdx_iter = sources[0].load_cdx(query)
    else:
        source_iters = map(lambda src: src.load_cdx(query), sources)
        cdx_iter = merge(*(source_iters))

    for cdx in cdx_iter:
        yield cdx


# =================================================================
def make_obj_iter(text_iter, query):
    """
    convert text cdx stream to CDXObject/IDXObject.
    """
    if query.secondary_index_only:
        cls = IDXObject
    else:
        cls = CDXObject

    return (cls(line) for line in text_iter)


# =================================================================
def cdx_limit(cdx_iter, limit):
    """
    limit cdx to at most `limit`.
    """
    return (cdx for cdx, _ in zip(cdx_iter, range(limit)))


# =================================================================
def cdx_reverse(cdx_iter, limit):
    """
    return cdx records in reverse order.
    """
    # optimize for single last
    if limit == 1:
        last = None

        for cdx in cdx_iter:
            last = cdx

        if not last:
            return
        yield last

    reverse_cdxs = deque(maxlen=limit)

    for cdx in cdx_iter:
        reverse_cdxs.appendleft(cdx)

    for cdx in reverse_cdxs:
        yield cdx


# =================================================================
def cdx_filter(cdx_iter, filter_strings):
    """
    filter CDX by regex if each filter is :samp:`{field}:{regex}` form,
    apply filter to :samp:`cdx[{field}]`.
    """
    # Support single strings as well
    if isinstance(filter_strings, str):
        filter_strings = [filter_strings]

    filters = []

    class Filter:
        def __init__(self, string):
            # invert filter
            self.invert = string.startswith('!')
            if self.invert:
                string = string[1:]

            # exact match
            if string.startswith('='):
                string = string[1:]
                self.compare_func = self.exact
            # contains match
            elif string.startswith('~'):
                string = string[1:]
                self.compare_func = self.contains
            else:
                self.compare_func = self.regex

            parts = string.split(':', 1)
            # no field set, apply filter to entire cdx
            if len(parts) == 1:
                self.field = ''
            # apply filter to cdx[field]
            else:
                self.field = parts[0]
                self.field = CDXObject.CDX_ALT_FIELDS.get(self.field,
                                                          self.field)
                string = parts[1]

            # make regex if regex mode
            if self.compare_func == self.regex:
                self.regex = re.compile(string)
            else:
                self.filter_str = string

        def __call__(self, cdx):
            if not self.field:
                val = str(cdx)
            else:
                val = cdx.get(self.field, '')

            matched = self.compare_func(val)

            return matched ^ self.invert

        def exact(self, val):
            return (self.filter_str == val)

        def contains(self, val):
            return (self.filter_str in val)

        def regex(self, val):
            return self.regex.match(val) is not None

    filters = list(map(Filter, filter_strings))

    for cdx in cdx_iter:
        if all(x(cdx) for x in filters):
            yield cdx


# =================================================================
def cdx_clamp(cdx_iter, from_ts, to_ts):
    """
    Clamp by start and end ts
    """
    if from_ts and len(from_ts) < 14:
        from_ts = pad_timestamp(from_ts, PAD_14_DOWN)

    if to_ts and len(to_ts) < 14:
        to_ts = pad_timestamp(to_ts, PAD_14_UP)

    for cdx in cdx_iter:
        if from_ts and cdx[TIMESTAMP] < from_ts:
            continue

        if to_ts and cdx[TIMESTAMP] > to_ts:
            continue

        yield cdx


# =================================================================
def cdx_collapse_time_status(cdx_iter, timelen=10):
    """
    collapse by timestamp and status code.
    """
    timelen = int(timelen)

    last_token = None

    for cdx in cdx_iter:
        curr_token = (cdx[TIMESTAMP][:timelen], cdx.get(STATUSCODE, ''))

        # yield if last_dedup_time is diff, otherwise skip
        if curr_token != last_token:
            last_token = curr_token
            yield cdx


# =================================================================
def cdx_sort_closest(closest, cdx_iter, limit=10):
    """
    sort CDXCaptureResult by closest to timestamp.
    """
    closest_cdx = []
    closest_keys = []
    closest_sec = timestamp_to_sec(closest)

    for cdx in cdx_iter:
        sec = timestamp_to_sec(cdx[TIMESTAMP])
        key = abs(closest_sec - sec)

        # create tuple to sort by key
        # bisect.insort(closest_cdx, (key, cdx))

        i = bisect.bisect_right(closest_keys, key)
        closest_keys.insert(i, key)
        closest_cdx.insert(i, cdx)

        if len(closest_cdx) == limit:
            # assuming cdx in ascending order and keys have started increasing
            if key > closest_keys[-1]:
                break

        if len(closest_cdx) > limit:
            closest_cdx.pop()

    for cdx in closest_cdx:
        yield cdx

        # for cdx in map(lambda x: x[1], closest_cdx):
        #    yield cdx


# =================================================================
# resolve revisits

# Fields to append from cdx original to revisit
ORIG_TUPLE = [LENGTH, OFFSET, FILENAME]


def cdx_resolve_revisits(cdx_iter):
    """
    resolve revisits.

    this filter adds three fields to CDX: ``orig.length``, ``orig.offset``,
    and ``orig.filename``. for revisit records, these fields have corresponding
    field values in previous non-revisit (original) CDX record.
    They are all ``"-"`` for non-revisit records.
    """
    originals = {}

    for cdx in cdx_iter:
        is_revisit = cdx.is_revisit()

        digest = cdx.get(DIGEST)

        original_cdx = None

        # only set if digest is valid, otherwise no way to resolve
        if digest:
            original_cdx = originals.get(digest)

            if not original_cdx and not is_revisit:
                originals[digest] = cdx

        if original_cdx and is_revisit:
            fill_orig = lambda field: original_cdx.get(field, '-')
            # Transfer mimetype and statuscode
            if MIMETYPE in cdx:
                cdx[MIMETYPE] = original_cdx.get(MIMETYPE, '')
            if STATUSCODE in cdx:
                cdx[STATUSCODE] = original_cdx.get(STATUSCODE, '')
        else:
            fill_orig = lambda field: '-'

        # Always add either the original or empty '- - -'
        for field in ORIG_TUPLE:
            cdx['orig.' + field] = fill_orig(field)

        yield cdx


# end pywb.cdx.cdxops

# begin pywb.cdx.query
# =================================================================
class CDXQuery(object):
    def __init__(self, params):
        self.params = params
        url = self.url
        url = self.params.get('alt_url', url)
        if not self.params.get('matchType'):
            if url.startswith('*.'):
                url = self.params['url'] = url[2:]
                self.params['matchType'] = 'domain'
            elif url.endswith('*'):
                url = self.params['url'] = url[:-1]
                self.params['matchType'] = 'prefix'
            else:
                self.params['matchType'] = 'exact'

        start, end = calc_search_range(url=url,
                                       match_type=self.params['matchType'],
                                       url_canon=self.params.get('_url_canon'))

        self.params['key'] = start.encode('utf-8')
        self.params['end_key'] = end.encode('utf-8')

    @property
    def key(self):
        return self.params['key']

    @property
    def end_key(self):
        return self.params['end_key']

    def set_key(self, key, end_key):
        self.params['key'] = key
        self.params['end_key'] = end_key

    @property
    def url(self):
        try:
            return self.params['url']
        except KeyError:
            msg = 'A url= param must be specified to query the cdx server'
            raise CDXException(msg)

    @property
    def match_type(self):
        return self.params.get('matchType', 'exact')

    @property
    def is_exact(self):
        return self.match_type == 'exact'

    @property
    def allow_fuzzy(self):
        return self._get_bool('allowFuzzy')

    @property
    def output(self):
        return self.params.get('output', 'text')

    @property
    def limit(self):
        return int(self.params.get('limit', 100000))

    @property
    def collapse_time(self):
        return self.params.get('collapseTime')

    @property
    def resolve_revisits(self):
        return self._get_bool('resolveRevisits')

    @property
    def filters(self):
        return self.params.get('filter', [])

    @property
    def fields(self):
        v = self.params.get('fields')
        # check old param name
        if not v:
            v = self.params.get('fl')
        return v.split(',') if v else None

    @property
    def from_ts(self):
        return self.params.get('from') or self.params.get('from_ts')

    @property
    def to_ts(self):
        return self.params.get('to')

    @property
    def closest(self):
        # sort=closest is not required
        return self.params.get('closest')

    @property
    def reverse(self):
        # sort=reverse overrides reverse=0
        return (self._get_bool('reverse') or
                self.params.get('sort') == 'reverse')

    @property
    def custom_ops(self):
        return self.params.get('custom_ops', [])

    @property
    def secondary_index_only(self):
        return self._get_bool('showPagedIndex')

    @property
    def page(self):
        return int(self.params.get('page', 0))

    @property
    def page_size(self):
        return self.params.get('pageSize')

    @property
    def page_count(self):
        return self._get_bool('showNumPages')

    def _get_bool(self, name, def_val=False):
        v = self.params.get(name)
        if v:
            try:
                v = int(v)
            except ValueError as ex:
                v = (v.lower() == 'true')
        else:
            v = def_val

        return bool(v)

    def urlencode(self):
        return urlencode(self.params, True)


# end pywb.cdx.query

# begin pywb.cdx.cdxsource
# =================================================================
class CDXSource(object):
    """
    Represents any cdx index source
    """

    def load_cdx(self, query):  # pragma: no cover
        raise NotImplementedError('Implement in subclass')


# =================================================================
class CDXFile(CDXSource):
    """
    Represents a local plain-text .cdx file
    """

    def __init__(self, filename):
        self.filename = filename

    def load_cdx(self, query):
        return self._do_load_file(self.filename, query)

    @staticmethod
    def _do_load_file(filename, query):
        with open(filename, 'rb') as source:
            gen = iter_range(source, query.key,
                             query.end_key)
            for line in gen:
                yield line

    def __str__(self):
        return 'CDX File - ' + self.filename


# =================================================================
class RemoteCDXSource(CDXSource):
    """
    Represents a remote cdx server, to which requests will be proxied.

    Only ``url`` and ``match_type`` params are proxied at this time,
    the stream is passed through all other filters locally.
    """

    def __init__(self, filename, cookie=None, remote_processing=False):
        self.remote_url = filename
        self.cookie = cookie
        self.remote_processing = remote_processing

    def load_cdx(self, query):
        if self.remote_processing:
            remote_query = query
        else:
            # Only send url and matchType to remote
            remote_query = CDXQuery(dict(url=query.url,
                                         matchType=query.match_type))

        urlparams = remote_query.urlencode()

        try:
            request = Request(self.remote_url + '?' + urlparams)

            if self.cookie:
                request.add_header('Cookie', self.cookie)

            response = urlopen(request)

        except HTTPError as e:
            if e.code == 403:
                raise AccessException('Access Denied')
            elif e.code == 404:
                # return empty list for consistency with other cdx sources
                # will be converted to 404 if no other retry
                return []
            elif e.code == 400:
                raise BadRequestException()
            else:
                raise WbException('Invalid response from remote cdx server')

        return iter(response)

    def __str__(self):
        if self.remote_processing:
            return 'Remote CDX Server: ' + self.remote_url
        else:
            return 'Remote CDX Source: ' + self.remote_url


# =================================================================
class RedisCDXSource(CDXSource):
    DEFAULT_KEY_PREFIX = b'c:'

    def __init__(self, redis_url, config=None):
        import redis

        parts = redis_url.split('/')
        if len(parts) > 4:
            self.cdx_key = parts[4].encode('utf-8')
            redis_url = 'redis://' + parts[2] + '/' + parts[3]
        else:
            self.cdx_key = None

        self.redis_url = redis_url
        self.redis = redis.StrictRedis.from_url(redis_url)

        self.key_prefix = self.DEFAULT_KEY_PREFIX

    def load_cdx(self, query):
        """
        Load cdx from redis cache, from an ordered list

        If cdx_key is set, treat it as cdx file and load use
        zrangebylex! (Supports all match types!)

        Otherwise, assume a key per-url and load all entries for that key.
        (Only exact match supported)
        """

        if self.cdx_key:
            return self.load_sorted_range(query, self.cdx_key)
        else:
            return self.load_single_key(query.key)

    def load_sorted_range(self, query, cdx_key):
        cdx_list = self.redis.zrangebylex(cdx_key,
                                          b'[' + query.key,
                                          b'(' + query.end_key)

        return iter(cdx_list)

    def load_single_key(self, key):
        # ensure only url/surt is part of key
        key = key.split(b' ')[0]
        cdx_list = self.redis.zrange(self.key_prefix + key, 0, -1)

        # key is not part of list, so prepend to each line
        key += b' '
        cdx_list = list(map(lambda x: key + x, cdx_list))
        return cdx_list

    def __str__(self):
        return 'Redis - ' + self.redis_url


# end pywb.cdx.cdxsource


# begin pywb.cdx.cdxdomainspecific
# =================================================================
def load_domain_specific_cdx_rules(ds_rules_file, surt_ordered):
    canon = None
    fuzzy = None

    # Load Canonicalizer Rules
    rules = RuleSet(CDXDomainSpecificRule, 'canonicalize',
                    ds_rules_file=ds_rules_file)

    if not surt_ordered:
        for rule in rules.rules:
            rule.unsurt()

    if rules:
        canon = CustomUrlCanonicalizer(rules, surt_ordered)

    # Load Fuzzy Lookup Rules
    rules = RuleSet(CDXDomainSpecificRule, 'fuzzy_lookup',
                    ds_rules_file=ds_rules_file)

    if not surt_ordered:
        for rule in rules.rules:
            rule.unsurt()

    if rules:
        fuzzy = FuzzyQuery(rules)

    logging.debug('CustomCanonilizer? ' + str(bool(canon)))
    logging.debug('FuzzyMatcher? ' + str(bool(canon)))
    return (canon, fuzzy)


# =================================================================
class CustomUrlCanonicalizer(UrlCanonicalizer):
    def __init__(self, rules, surt_ordered=True):
        super(CustomUrlCanonicalizer, self).__init__(surt_ordered)
        self.rules = rules

    def __call__(self, url):
        urlkey = super(CustomUrlCanonicalizer, self).__call__(url)

        for rule in self.rules.iter_matching(urlkey):
            m = rule.regex.match(urlkey)
            if not m:
                continue

            if rule.replace:
                return m.expand(rule.replace)

        return urlkey


# =================================================================
class FuzzyQuery(object):
    def __init__(self, rules):
        self.rules = rules

    def __call__(self, query):
        matched_rule = None

        urlkey = to_native_str(query.key, 'utf-8')
        url = query.url
        filter_ = query.filters
        output = query.output

        for rule in self.rules.iter_matching(urlkey):
            m = rule.regex.search(urlkey)
            if not m:
                continue

            matched_rule = rule

            groups = m.groups()
            for g in groups:
                for f in matched_rule.filter:
                    filter_.append(f.format(g))

            break

        if not matched_rule:
            return None

        repl = '?'
        if matched_rule.replace:
            repl = matched_rule.replace

        inx = url.find(repl)
        if inx > 0:
            url = url[:inx + len(repl)]

        if matched_rule.match_type == 'domain':
            host = urlsplit(url).netloc
            # remove the subdomain
            url = host.split('.', 1)[1]

        params = query.params
        params.update({'url': url,
                       'matchType': matched_rule.match_type,
                       'filter': filter_})

        if 'reverse' in params:
            del params['reverse']

        if 'closest' in params:
            del params['closest']

        if 'end_key' in params:
            del params['end_key']

        return params


# =================================================================
class CDXDomainSpecificRule(BaseRule):
    DEFAULT_FILTER = ['~urlkey:{0}']
    DEFAULT_MATCH_TYPE = 'prefix'

    def __init__(self, name, config):
        super(CDXDomainSpecificRule, self).__init__(name, config)

        if not isinstance(config, dict):
            self.regex = self.make_regex(config)
            self.replace = None
            self.filter = self.DEFAULT_FILTER
            self.match_type = self.DEFAULT_MATCH_TYPE
        else:
            self.regex = self.make_regex(config.get('match'))
            self.replace = config.get('replace')
            self.filter = config.get('filter', self.DEFAULT_FILTER)
            self.match_type = config.get('type', self.DEFAULT_MATCH_TYPE)

    def unsurt(self):
        """
        urlkey is assumed to be in surt format by default
        In the case of non-surt format, this method is called
        to desurt any urls
        """
        self.url_prefix = list(map(unsurt, self.url_prefix))
        if self.regex:
            self.regex = re.compile(unsurt(self.regex.pattern))

        if self.replace:
            self.replace = unsurt(self.replace)

    @staticmethod
    def make_regex(config):
        # just query args
        if isinstance(config, list):
            string = CDXDomainSpecificRule.make_query_match_regex(config)

        # split out base and args
        elif isinstance(config, dict):
            string = config.get('regex', '')
            string += CDXDomainSpecificRule.make_query_match_regex(
                config.get('args', []))

        # else assume string
        else:
            string = str(config)

        return re.compile(string)

    @staticmethod
    def make_query_match_regex(params_list):
        params_list.sort()

        def conv(value):
            return '[?&]({0}=[^&]+)'.format(re.escape(value))

        params_list = list(map(conv, params_list))
        final_str = '.*'.join(params_list)
        return final_str


# end pywb.cdx.cdxdomainspecific


# begin pywb.cdx.zipnum
# =================================================================
class ZipBlocks:
    def __init__(self, part, offset, length, count):
        self.part = part
        self.offset = offset
        self.length = length
        self.count = count


# =================================================================
# TODO: see if these could be combined with warc path resolvers

class LocMapResolver(object):
    """ Lookup shards based on a file mapping
    shard name to one or more paths. The entries are
    tab delimited.
    """

    def __init__(self, loc_summary, loc_filename):
        # initial loc map
        self.loc_map = {}
        self.loc_mtime = 0
        if not loc_filename:
            splits = os.path.splitext(loc_summary)
            loc_filename = splits[0] + '.loc'
        self.loc_filename = loc_filename

        self.load_loc()

    def load_loc(self):
        # check modified time of current file before loading
        new_mtime = os.path.getmtime(self.loc_filename)
        if (new_mtime == self.loc_mtime):
            return

        # update loc file mtime
        self.loc_mtime = new_mtime

        local_dir = os.path.dirname(self.loc_filename)

        def res_path(pathname):
            if '://' not in pathname:
                pathname = os.path.join(local_dir, pathname)
            return pathname

        logging.debug('Loading loc from: ' + self.loc_filename)
        with open(self.loc_filename, 'r') as fh:
            for line in fh:
                parts = line.rstrip().split('\t')

                paths = [res_path(pathname) for pathname in parts[1:]]
                self.loc_map[parts[0]] = paths

    def __call__(self, part, query):
        return self.loc_map[part]


# =================================================================
class LocPrefixResolver(object):
    """ Use a prefix lookup, where the prefix can either be a fixed
    string or can be a regex replacement of the index summary path
    """

    def __init__(self, loc_summary, loc_config):
        import re
        loc_match = loc_config.get('match', '().*')
        loc_replace = loc_config['replace']
        loc_summary = os.path.dirname(loc_summary) + '/'
        self.prefix = re.sub(loc_match, loc_replace, loc_summary)

    def load_loc(self):
        pass

    def __call__(self, part, query):
        return [self.prefix + part]


# =================================================================
class ZipNumCluster(CDXSource):
    DEFAULT_RELOAD_INTERVAL = 10  # in minutes
    DEFAULT_MAX_BLOCKS = 10

    def __init__(self, summary, config=None):
        self.max_blocks = self.DEFAULT_MAX_BLOCKS

        self.loc_resolver = None

        loc = None
        cookie_maker = None
        reload_ival = self.DEFAULT_RELOAD_INTERVAL

        if config:
            loc = config.get('shard_index_loc')
            cookie_maker = config.get('cookie_maker')

            self.max_blocks = config.get('max_blocks', self.max_blocks)

            reload_ival = config.get('reload_interval', reload_ival)

        if isinstance(loc, dict):
            self.loc_resolver = LocPrefixResolver(summary, loc)
        else:
            self.loc_resolver = LocMapResolver(summary, loc)

        self.summary = summary

        # reload interval
        self.loc_update_time = datetime.datetime.now()
        self.reload_interval = datetime.timedelta(minutes=reload_ival)

        self.blk_loader = BlockLoader(cookie_maker=cookie_maker)

    #    @staticmethod
    #    def reload_timed(timestamp, val, delta, func):
    #        now = datetime.datetime.now()
    #        if now - timestamp >= delta:
    #            func()
    #            return now
    #        return None
    #
    #    def reload_loc(self):
    #        reload_time = self.reload_timed(self.loc_update_time,
    #                                        self.loc_map,
    #                                        self.reload_interval,
    #                                        self.load_loc)
    #
    #        if reload_time:
    #            self.loc_update_time = reload_time

    def load_cdx(self, query):
        self.loc_resolver.load_loc()
        return self._do_load_cdx(self.summary, query)

    def _do_load_cdx(self, filename, query):
        reader = open(filename, 'rb')

        idx_iter = self.compute_page_range(reader, query)

        if query.secondary_index_only or query.page_count:
            return idx_iter

        blocks = self.idx_to_cdx(idx_iter, query)

        def gen_cdx():
            for blk in blocks:
                for cdx in blk:
                    yield cdx

        return gen_cdx()

    def _page_info(self, pages, pagesize, blocks):
        info = dict(pages=pages,
                    pageSize=pagesize,
                    blocks=blocks)
        return json.dumps(info) + '\n'

    def compute_page_range(self, reader, query):
        pagesize = query.page_size
        if not pagesize:
            pagesize = self.max_blocks
        else:
            pagesize = int(pagesize)

        last_line = None

        # Get End
        end_iter = search(reader, query.end_key, prev_size=1)

        try:
            end_line = six.next(end_iter)
        except StopIteration:
            last_line = read_last_line(reader)
            end_line = last_line

        # Get Start
        first_iter = iter_range(reader,
                                query.key,
                                query.end_key,
                                prev_size=1)

        try:
            first_line = six.next(first_iter)
        except StopIteration:
            if end_line == last_line and query.key >= last_line:
                first_line = last_line
            else:
                reader.close()
                if query.page_count:
                    yield self._page_info(0, pagesize, 0)
                    return
                else:
                    raise

        first = IDXObject(first_line)

        end = IDXObject(end_line)

        try:
            blocks = end['lineno'] - first['lineno']
            total_pages = int(blocks / pagesize) + 1
        except:
            blocks = -1
            total_pages = 1

        if query.page_count:
            # same line, so actually need to look at cdx
            # to determine if it exists
            if blocks == 0:
                try:
                    block_cdx_iter = self.idx_to_cdx([first_line], query)
                    block = six.next(block_cdx_iter)
                    cdx = six.next(block)
                except StopIteration:
                    total_pages = 0
                    blocks = -1

            yield self._page_info(total_pages, pagesize, blocks + 1)
            reader.close()
            return

        curr_page = query.page
        if curr_page >= total_pages or curr_page < 0:
            msg = 'Page {0} invalid: First Page is 0, Last Page is {1}'
            reader.close()
            raise CDXException(msg.format(curr_page, total_pages - 1))

        startline = curr_page * pagesize
        endline = startline + pagesize - 1
        if blocks >= 0:
            endline = min(endline, blocks)

        if curr_page == 0:
            yield first_line
        else:
            startline -= 1

        idxiter = itertools.islice(first_iter, startline, endline)
        for idx in idxiter:
            yield idx

        reader.close()

    def search_by_line_num(self, reader, line):  # pragma: no cover
        def line_cmp(line1, line2):
            line1_no = int(line1.rsplit(b'\t', 1)[-1])
            line2_no = int(line2.rsplit(b'\t', 1)[-1])
            return cmp(line1_no, line2_no)

        line_iter = search(reader, line, compare_func=line_cmp)
        yield six.next(line_iter)

    def idx_to_cdx(self, idx_iter, query):
        blocks = None
        ranges = []

        for idx in idx_iter:
            idx = IDXObject(idx)

            if (blocks and blocks.part == idx['part'] and
                            blocks.offset + blocks.length == idx['offset'] and
                        blocks.count < self.max_blocks):

                blocks.length += idx['length']
                blocks.count += 1
                ranges.append(idx['length'])

            else:
                if blocks:
                    yield self.block_to_cdx_iter(blocks, ranges, query)

                blocks = ZipBlocks(idx['part'],
                                   idx['offset'],
                                   idx['length'],
                                   1)

                ranges = [blocks.length]

        if blocks:
            yield self.block_to_cdx_iter(blocks, ranges, query)

    def block_to_cdx_iter(self, blocks, ranges, query):
        last_exc = None
        last_traceback = None

        try:
            locations = self.loc_resolver(blocks.part, query)
        except:
            raise Exception('No Locations Found for: ' + blocks.part)

        for location in self.loc_resolver(blocks.part, query):
            try:
                return self.load_blocks(location, blocks, ranges, query)
            except Exception as exc:
                last_exc = exc
                import sys
                last_traceback = sys.exc_info()[2]

        if last_exc:
            six.reraise(Exception, last_exc, last_traceback)
            # raise last_exc
        else:
            raise Exception('No Locations Found for: ' + blocks.part)

    def load_blocks(self, location, blocks, ranges, query):
        """ Load one or more blocks of compressed cdx lines, return
        a line iterator which decompresses and returns one line at a time,
        bounded by query.key and query.end_key
        """

        if (logging.getLogger().getEffectiveLevel() <= logging.DEBUG):
            msg = 'Loading {b.count} blocks from {loc}:{b.offset}+{b.length}'
            logging.debug(msg.format(b=blocks, loc=location))

        reader = self.blk_loader.load(location, blocks.offset, blocks.length)

        def decompress_block(range_):
            decomp = gzip_decompressor()
            buff = decomp.decompress(reader.read(range_))
            for line in BytesIO(buff):
                yield line

        iter_ = itertools.chain(*map(decompress_block, ranges))

        # start bound
        iter_ = linearsearch(iter_, query.key)

        # end bound
        iter_ = itertools.takewhile(lambda line: line < query.end_key, iter_)
        return iter_

    def __str__(self):
        return 'ZipNum Cluster: {0}, {1}'.format(self.summary,
                                                 self.loc_resolver)


# end pywb.cdx.zipnum


# begin pywb.cdx.cdxserver
# =================================================================
class BaseCDXServer(object):
    def __init__(self, **kwargs):
        ds_rules_file = kwargs.get('ds_rules_file')
        surt_ordered = kwargs.get('surt_ordered', True)

        # load from domain-specific rules
        if ds_rules_file:
            self.url_canon, self.fuzzy_query = (
                load_domain_specific_cdx_rules(ds_rules_file, surt_ordered))
        # or custom passed in canonicalizer
        else:
            self.url_canon = kwargs.get('url_canon')
            self.fuzzy_query = kwargs.get('fuzzy_query')

        # set default canonicalizer if none set thus far
        if not self.url_canon:
            self.url_canon = UrlCanonicalizer(surt_ordered)

    def _check_cdx_iter(self, cdx_iter, query):
        """ Check cdx iter semantics
        If `cdx_iter` is empty (no matches), check if fuzzy matching
        is allowed, and try it -- otherwise,
        throw :exc:`~pywb.utils.wbexception.NotFoundException`
        """

        cdx_iter = self.peek_iter(cdx_iter)

        if cdx_iter:
            return cdx_iter

        # check if fuzzy is allowed and ensure that its an
        # exact match
        if (self.fuzzy_query and
                query.allow_fuzzy and
                query.is_exact):

            fuzzy_query_params = self.fuzzy_query(query)
            if fuzzy_query_params:
                return self.load_cdx(**fuzzy_query_params)

        msg = 'No Captures found for: ' + query.url
        if not query.is_exact:
            msg += ' (' + query.match_type + ' query)'

        raise NotFoundException(msg, url=query.url)

    # def _calc_search_keys(self, query):
    #    return calc_search_range(url=query.url,
    #                             match_type=query.match_type,
    #                             url_canon=self.url_canon)

    def load_cdx(self, **params):
        params['_url_canon'] = self.url_canon
        query = CDXQuery(params)

        # key, end_key = self._calc_search_keys(query)
        # query.set_key(key, end_key)

        cdx_iter = self._load_cdx_query(query)

        return self._check_cdx_iter(cdx_iter, query)

    def _load_cdx_query(self, query):  # pragma: no cover
        raise NotImplementedError('Implement in subclass')

    @staticmethod
    def peek_iter(iterable):
        try:
            first = next(iterable)
        except StopIteration:
            return None

        return chain([first], iterable)


# =================================================================
class CDXServer(BaseCDXServer):
    """
    Top-level cdx server object which maintains a list of cdx sources,
    responds to queries and dispatches to the cdx ops for processing
    """

    def __init__(self, paths, **kwargs):
        super(CDXServer, self).__init__(**kwargs)
        # TODO: we could save config in member, so that other
        # methods can use it. it's bad for add_cdx_source to take
        # config argument.
        self._create_cdx_sources(paths, kwargs.get('config'))

    def _load_cdx_query(self, query):
        """
        load CDX for query parameters ``params``.
        ``key`` (or ``url``) parameter specifies URL to query,
        ``matchType`` parameter specifies matching method for ``key``
        (default ``exact``).
        other parameters are passed down to :func:`cdx_load`.
        raises :exc:`~pywb.utils.wbexception.NotFoundException`
        if no captures are found.

        :param query: query parameters
        :type query: :class:`~pywb.cdx.query.CDXQuery`
        :rtype: iterator on :class:`~pywb.cdx.cdxobject.CDXObject`
        """
        return cdx_load(self.sources, query)

    def _create_cdx_sources(self, paths, config):
        """
        build CDXSource instances for each of path in ``paths``.

        :param paths: list of sources or single source.
        each source may be either string or CDXSource instance. value
        of any other types will be silently ignored.
        :param config: config object passed to :method:`add_cdx_source`.
        """
        self.sources = []

        if paths is not None:
            if not isinstance(paths, (list, tuple)):
                paths = [paths]

            for path in paths:
                self.add_cdx_source(path, config)

        if len(self.sources) == 0:
            logging.warn('No CDX Sources configured from paths=%s', paths)

    def _add_cdx_source(self, source):
        if source is None:
            return

        logging.debug('Adding CDX Source: %s', source)
        self.sources.append(source)

    def add_cdx_source(self, source, config):
        if isinstance(source, CDXSource):
            self._add_cdx_source(source)

        elif isinstance(source, str):
            if os.path.isdir(source):
                for fn in os.listdir(source):
                    self._add_cdx_source(self._create_cdx_source(
                        os.path.join(source, fn), config))
            else:
                self._add_cdx_source(self._create_cdx_source(
                    source, config))

    def _create_cdx_source(self, filename, config):
        if is_http(filename):
            return RemoteCDXSource(filename)

        if filename.startswith('redis://'):
            return RedisCDXSource(filename, config)

        if filename.endswith(('.cdx', '.cdxj')):
            return CDXFile(filename)

        if filename.endswith(('.summary', '.idx')):
            return ZipNumCluster(filename, config)

        # no warning for .loc or .gz (zipnum)
        if not filename.endswith(('.loc', '.gz')):
            logging.warn('skipping unrecognized URI: %s', filename)

        return None


# =================================================================
class RemoteCDXServer(BaseCDXServer):
    """
    A special cdx server that uses a single
    :class:`~pywb.cdx.cdxsource.RemoteCDXSource`.
    It simply proxies the query params to the remote source
    and performs no local processing/filtering
    """

    def __init__(self, source, **kwargs):
        super(RemoteCDXServer, self).__init__(**kwargs)

        if isinstance(source, RemoteCDXSource):
            self.source = source
        elif (isinstance(source, str) and is_http(source)):
            self.source = RemoteCDXSource(source, remote_processing=True)
        else:
            raise Exception('Invalid remote cdx source: ' + str(source))

    def _load_cdx_query(self, query):
        return cdx_load([self.source], query, process=False)


# =================================================================
def create_cdx_server(config, ds_rules_file=None, server_cls=None):
    if hasattr(config, 'get'):
        paths = config.get('index_paths')
        surt_ordered = config.get('surt_ordered', True)
        pass_config = config
    else:
        paths = config
        surt_ordered = True
        pass_config = None

    logging.debug('CDX Surt-Ordered? ' + str(surt_ordered))

    if not server_cls:
        if ((isinstance(paths, str) and is_http(paths)) or
                isinstance(paths, RemoteCDXSource)):
            server_cls = RemoteCDXServer
        else:
            server_cls = CDXServer

    return server_cls(paths,
                      config=pass_config,
                      surt_ordered=surt_ordered,
                      ds_rules_file=ds_rules_file)


# end pywb.cdx.cdxserver

# begin pywb.manager.migrate
class MigrateCDX(object):
    def __init__(self, dir_):
        self.cdx_dir = dir_

    def iter_cdx_files(self):
        for root, dirs, files in os.walk(self.cdx_dir):
            for filename in files:
                if filename.endswith('.cdx'):
                    full_path = os.path.join(root, filename)
                    yield full_path

    def count_cdx(self):
        count = 0
        for x in self.iter_cdx_files():
            count += 1
        return count

    def convert_to_cdxj(self):
        cdxj_writer = CDXJ()
        for filename in self.iter_cdx_files():
            outfile = filename + 'j'

            print('Converting {0} -> {1}'.format(filename, outfile))

            with open(outfile + '.tmp', 'w+') as out:
                with open(filename, 'rb') as fh:
                    for line in fh:
                        if line.startswith(b' CDX'):
                            continue
                        cdx = CDXObject(line)
                        cdx[URLKEY] = canonicalize(cdx[ORIGINAL])
                        cdxj_writer.write_cdx_line(out, cdx, cdx['filename'])

            shutil.move(outfile + '.tmp', outfile)
            os.remove(filename)
# end pywb.manager.migrate

# begin pywb.manager.autoindex
#=============================================================================
class CDXAutoIndexer(RegexMatchingEventHandler):
    def __init__(self, updater, path):
        super(CDXAutoIndexer, self).__init__(regexes=[EXT_REGEX],
                                             ignore_directories=True)
        self.updater = updater
        self.cdx_path = path

    def on_created(self, event):
        self.updater(event.src_path)

    def on_modified(self, event):
        self.updater(event.src_path)

    def start_watch(self):
        self.observer = Observer()
        self.observer.schedule(self, self.cdx_path, recursive=True)
        self.observer.start()

    def do_loop(self, sleep_time=1):
        try:
            while keep_running:
                time.sleep(sleep_time)
        except KeyboardInterrupt:  # pragma: no cover
            self.observer.stop()
            self.observer.join()


# end pywb.manager.autoindex

# begin pywb.manager.manager
#=============================================================================
# to allow testing by mocking get_input
def get_input(msg):  #pragma: no cover
    return raw_input(msg)


#=============================================================================
class CollectionsManager(object):
    """ This utility is designed to
simplify the creation and management of web archive collections

It may be used via cmdline to setup and maintain the
directory structure expected by pywb
    """
    DEF_INDEX_FILE = 'index.cdxj'
    AUTO_INDEX_FILE = 'autoindex.cdxj'

    COLL_RX = re.compile('^[\w][-\w]*$')

    def __init__(self, coll_name, colls_dir='collections', must_exist=True):
        self.default_config = load_yaml_config(DEFAULT_CONFIG)

        if coll_name and not self.COLL_RX.match(coll_name):
            raise ValueError('Invalid Collection Name: ' + coll_name)

        self.colls_dir = os.path.join(os.getcwd(), colls_dir)

        self._set_coll_dirs(coll_name)

        if must_exist:
            self._assert_coll_exists()

    def _set_coll_dirs(self, coll_name):
        self.coll_name = coll_name
        self.curr_coll_dir = os.path.join(self.colls_dir, coll_name)

        self.archive_dir = self._get_dir('archive_paths')

        self.indexes_dir = self._get_dir('index_paths')
        self.static_dir = self._get_dir('static_path')
        self.templates_dir = self._get_dir('templates_dir')

    def list_colls(self):
        print('Collections:')
        if not os.path.isdir(self.colls_dir):
            msg = ('"Collections" directory not found. ' +
                   'To create a new collection, run:\n\n{0} init <name>')
            raise IOError(msg.format(sys.argv[0]))
        for d in os.listdir(self.colls_dir):
            if os.path.isdir(os.path.join(self.colls_dir, d)):
                print('- ' + d)

    def _get_root_dir(self, name):
        return os.path.join(os.getcwd(),
                            self.default_config['paths'][name])

    def _get_dir(self, name):
        return os.path.join(self.curr_coll_dir,
                            self.default_config['paths'][name])

    def _create_dir(self, dirname):
        if not os.path.isdir(dirname):
            os.mkdir(dirname)

        logging.info('Created Directory: ' + dirname)

    def add_collection(self):
        os.makedirs(self.curr_coll_dir)
        logging.info('Created Directory: ' + self.curr_coll_dir)

        self._create_dir(self.archive_dir)
        self._create_dir(self.indexes_dir)
        self._create_dir(self.static_dir)
        self._create_dir(self.templates_dir)

        self._create_dir(self._get_root_dir('static_path'))
        self._create_dir(self._get_root_dir('templates_dir'))

    def _assert_coll_exists(self):
        if not os.path.isdir(self.curr_coll_dir):
            msg = ('Collection {0} does not exist. ' +
                   'To create a new collection, run\n\n{1} init {0}')
            raise IOError(msg.format(self.coll_name, sys.argv[0]))

    def add_warcs(self, warcs):
        if not os.path.isdir(self.archive_dir):
            raise IOError('Directory {0} does not exist'.
                          format(self.archive_dir))

        full_paths = []
        for filename in warcs:
            filename = os.path.abspath(filename)
            shutil.copy2(filename, self.archive_dir)
            full_paths.append(os.path.join(self.archive_dir, filename))
            logging.info('Copied ' + filename + ' to ' + self.archive_dir)

        self._index_merge_warcs(full_paths, self.DEF_INDEX_FILE)

    def reindex(self):
        cdx_file = os.path.join(self.indexes_dir, self.DEF_INDEX_FILE)
        logging.info('Indexing ' + self.archive_dir + ' to ' + cdx_file)
        self._cdx_index(cdx_file, [self.archive_dir])

    def _cdx_index(self, out, input_, rel_root=None):
        options = dict(append_post=True,
                       cdxj=True,
                       sort=True,
                       recurse=True,
                       rel_root=rel_root)

        write_multi_cdx_index(out, input_, **options)

    def index_merge(self, filelist, index_file):
        wrongdir = 'Skipping {0}, must be in {1} archive directory'
        notfound = 'Skipping {0}, file not found'

        filtered_warcs = []

        # Check that warcs are actually in archive dir
        abs_archive_dir = os.path.abspath(self.archive_dir)

        for f in filelist:
            abs_filepath = os.path.abspath(f)
            prefix = os.path.commonprefix([abs_archive_dir, abs_filepath])

            if prefix != abs_archive_dir:
                raise IOError(wrongdir.format(abs_filepath, abs_archive_dir))
            elif not os.path.isfile(abs_filepath):
                raise IOError(notfound.format(f))
            else:
                filtered_warcs.append(abs_filepath)

        self._index_merge_warcs(filtered_warcs, index_file, abs_archive_dir)

    def _index_merge_warcs(self, new_warcs, index_file, rel_root=None):
        cdx_file = os.path.join(self.indexes_dir, index_file)

        temp_file = cdx_file + '.tmp.' + timestamp20_now()
        self._cdx_index(temp_file, new_warcs, rel_root)

        # no existing file, so just make it the new file
        if not os.path.isfile(cdx_file):
            shutil.move(temp_file, cdx_file)
            return

        merged_file = temp_file + '.merged'

        last_line = None

        with open(cdx_file, 'rb') as orig_index:
            with open(temp_file, 'rb') as new_index:
                with open(merged_file, 'w+b') as merged:
                    for line in heapq.merge(orig_index, new_index):
                        if last_line != line:
                            merged.write(line)
                            last_line = line

        shutil.move(merged_file, cdx_file)
        #os.rename(merged_file, cdx_file)
        os.remove(temp_file)

    def set_metadata(self, namevalue_pairs):
        metadata_yaml = os.path.join(self.curr_coll_dir, 'metadata.yaml')
        metadata = None
        if os.path.isfile(metadata_yaml):
            with open(metadata_yaml, 'rb') as fh:
                metadata = yaml.safe_load(fh)

        if not metadata:
            metadata = {}

        msg = 'Metadata params must be in the form "name=value"'
        for pair in namevalue_pairs:
            v = pair.split('=', 1)
            if len(v) != 2:
                raise ValueError(msg)

            print('Set {0}={1}'.format(v[0], v[1]))
            metadata[v[0]] = v[1]

        with open(metadata_yaml, 'w+b') as fh:
            fh.write(yaml.dump(metadata, default_flow_style=False).encode('utf-8'))

    def _load_templates_map(self):
        defaults = load_yaml_config(DEFAULT_CONFIG)

        temp_dir = defaults['paths']['templates_dir']

        # Coll Templates
        templates = defaults['paths']['template_files']

        for name, _ in six.iteritems(templates):
            templates[name] = os.path.join(temp_dir, defaults[name])

        # Shared Templates
        shared_templates = defaults['paths']['shared_template_files']

        for name, _ in six.iteritems(shared_templates):
            shared_templates[name] = os.path.join(temp_dir, defaults[name])

        return templates, shared_templates

    def list_templates(self):
        templates, shared_templates = self._load_templates_map()

        print('Shared Templates')
        for n, v in six.iteritems(shared_templates):
            print('- {0}: (pywb/{1})'.format(n, v))

        print('')

        print('Collection Templates')
        for n, v in six.iteritems(templates):
            print('- {0}: (pywb/{1})'.format(n, v))

    def _confirm_overwrite(self, full_path, msg):
        if not os.path.isfile(full_path):
            return True

        res = get_input(msg)
        try:
            res = strtobool(res)
        except ValueError:
            res = False

        if not res:
            raise IOError('Skipping, {0} already exists'.format(full_path))

    def _get_template_path(self, template_name, verb):
        templates, shared_templates = self._load_templates_map()

        try:
            filename = templates[template_name]
            if not self.coll_name:
                full_path = os.path.join(os.getcwd(), filename)
            else:
                full_path = os.path.join(self.templates_dir,
                                         os.path.basename(filename))

        except KeyError:
            try:
                filename = shared_templates[template_name]
                full_path = os.path.join(os.getcwd(), filename)

            except KeyError:
                msg = 'template name must be one of {0} or {1}'
                msg = msg.format(templates.keys(), shared_templates.keys())
                raise KeyError(msg)

        return full_path, filename

    def add_template(self, template_name, force=False):
        full_path, filename = self._get_template_path(template_name, 'add')

        msg = ('Template file "{0}" ({1}) already exists. ' +
               'Overwrite with default template? (y/n) ')
        msg = msg.format(full_path, template_name)

        if not force:
            self._confirm_overwrite(full_path, msg)

        data = resource_string('pywb', filename)
        with open(full_path, 'w+b') as fh:
            fh.write(data)

        full_path = os.path.abspath(full_path)
        msg = 'Copied default template "{0}" to "{1}"'
        print(msg.format(filename, full_path))

    def remove_template(self, template_name, force=False):
        full_path, filename = self._get_template_path(template_name, 'remove')

        if not os.path.isfile(full_path):
            msg = 'Template "{0}" does not exist.'
            raise IOError(msg.format(full_path))

        msg = 'Delete template file "{0}" ({1})? (y/n) '
        msg = msg.format(full_path, template_name)

        if not force:
            self._confirm_overwrite(full_path, msg)

        os.remove(full_path)
        print('Removed template file "{0}"'.format(full_path))

    def migrate_cdxj(self, path, force=False):
        migrate = MigrateCDX(path)
        count = migrate.count_cdx()
        if count == 0:
            print('Index files up-to-date, nothing to convert')
            return

        msg = 'Convert {0} index files? (y/n)'.format(count)
        if not force:
            res = get_input(msg)
            try:
                res = strtobool(res)
            except ValueError:
                res = False

            if not res:
                return

        migrate.convert_to_cdxj()

    def autoindex(self, do_loop=True):
        if self.coll_name:
            any_coll = False
            path = self.archive_dir
        else:
            path = self.colls_dir
            any_coll = True

        def do_index(warc):
            if any_coll:
                coll_name = warc.split(self.colls_dir + os.path.sep)
                coll_name = coll_name[-1].split(os.path.sep)[0]

                if coll_name != self.coll_name:
                    self._set_coll_dirs(coll_name)

            print('Auto-Indexing: ' + warc)
            self.index_merge([warc], self.AUTO_INDEX_FILE)
            print('Done.. Waiting for file updates')


        indexer = CDXAutoIndexer(do_index, path)
        indexer.start_watch()
        if do_loop:
            indexer.do_loop()

# end pywb.manager.manager

# begin pywb.perms.perms_filter
# =================================================================
def make_perms_cdx_filter(perms_policy, wbrequest):
    """
    Called internally to convert a perms_policy and a request
    to a filter which can be applied on the cdx
    """
    perms_checker = perms_policy(wbrequest)
    if not perms_checker:
        return None

    return _create_cdx_perms_filter(perms_checker)


# =================================================================
def _create_cdx_perms_filter(perms_checker):
    """
    Return a function which will filter the cdx given
    a Perms object.
    :param perms_checker: a Perms object which implements the
        allow_url_lookup() and access_check_capture() methods
    """

    def perms_filter_op(cdx_iter, query):
        """
        filter out those cdx records that user doesn't have access to,
        by consulting :param perms_checker:.
        :param cdx_iter: cdx record source iterable
        :param query: request parameters (CDXQuery)
        :param perms_checker: object implementing permission checker
        """
        if not perms_checker.allow_url_lookup(query.key):
            if query.is_exact:
                raise AccessException('Excluded')

        for cdx in cdx_iter:
            cdx = perms_checker.access_check_capture(cdx)
            if cdx:
                yield cdx

    return perms_filter_op


# ================================================================
def allow_all_perms_policy(wbrequest):
    """
    Perms policy which always returns a default Perms object
    which allows everything.

    The perms object is created per request and may store request
    state, if necessary.

    The same perms object may be called with multiple queries
    (such as for each cdx line) per request.
    """
    return Perms()


# =================================================================
class Perms(object):
    """
    A base perms checker which allows everything
    """

    def allow_url_lookup(self, key):
        """
        Return true/false if urlkey (canonicalized url)
        should be allowed.

        Default: allow all
        """
        return True

    def access_check_capture(self, cdx):
        """
        Allow/deny specified cdx capture (dict) to be included
        in the result.
        Return None to reject, or modify the cdx to exclude
        any fields that need to be restricted.

        Default: allow cdx line without modifications
        """
        return cdx


# end pywb.perms.perms_filter

# begin pywb.rewrite.cookie_rewriter

# ================================================================
class WbUrlBaseCookieRewriter(object):
    """ Base Cookie rewriter for wburl-based requests.
    """
    UTC_RX = re.compile('((?:.*)Expires=(?:.*))UTC', re.I)

    def __init__(self, url_rewriter):
        self.url_rewriter = url_rewriter

    def rewrite(self, cookie_str, header='Set-Cookie'):
        results = []
        cookie_str = self.UTC_RX.sub('\\1GMT', cookie_str)
        try:
            cookie = SimpleCookie(cookie_str)
        except CookieError:
            import traceback
            traceback.print_exc()
            return results

        for name, morsel in six.iteritems(cookie):
            morsel = self.rewrite_cookie(name, morsel)

            self._filter_morsel(morsel)
            results.append((header, morsel.OutputString()))

        return results

    def _filter_morsel(self, morsel):
        path = morsel.get('path')
        if path:
            inx = path.find(self.url_rewriter.rel_prefix)
            if inx > 0:
                morsel['path'] = path[inx:]

        if not self.url_rewriter.full_prefix.startswith('https://'):
            # also remove secure to avoid issues when
            # proxying over plain http
            if morsel.get('secure'):
                del morsel['secure']

        if not self.url_rewriter.rewrite_opts.get('is_live'):
            self._remove_age_opts(morsel)

    def _remove_age_opts(self, morsel):
        # remove expires as it refers to archived time
        if morsel.get('expires'):
            del morsel['expires']

        # don't use max-age, just expire at end of session
        if morsel.get('max-age'):
            del morsel['max-age']


# =================================================================
class RemoveAllCookiesRewriter(WbUrlBaseCookieRewriter):
    def rewrite(self, cookie_str, header='Set-Cookie'):
        return []


# =================================================================
class MinimalScopeCookieRewriter(WbUrlBaseCookieRewriter):
    """
    Attempt to rewrite cookies to minimal scope possible

    If path present, rewrite path to current rewritten url only
    If domain present, remove domain and set to path prefix
    """

    def rewrite_cookie(self, name, morsel):
        # if domain set, no choice but to expand cookie path to root
        if morsel.get('domain'):
            del morsel['domain']
            morsel['path'] = self.url_rewriter.rel_prefix
        # else set cookie to rewritten path
        elif morsel.get('path'):
            morsel['path'] = self.url_rewriter.rewrite(morsel['path'])

        return morsel


# =================================================================
class HostScopeCookieRewriter(WbUrlBaseCookieRewriter):
    """
    Attempt to rewrite cookies to current host url..

    If path present, rewrite path to current host. Only makes sense in live
    proxy or no redirect mode, as otherwise timestamp may change.

    If domain present, remove domain and set to path prefix
    """

    def rewrite_cookie(self, name, morsel):
        # if domain set, expand cookie to host prefix
        if morsel.get('domain'):
            del morsel['domain']
            morsel['path'] = self.url_rewriter.rewrite('/')

        # set cookie to rewritten path
        elif morsel.get('path'):
            morsel['path'] = self.url_rewriter.rewrite(morsel['path'])

        return morsel


# =================================================================
class ExactPathCookieRewriter(WbUrlBaseCookieRewriter):
    """
    Rewrite cookies only using exact path, useful for live rewrite
    without a timestamp and to minimize cookie pollution

    If path or domain present, simply remove
    """

    def rewrite_cookie(self, name, morsel):
        if morsel.get('domain'):
            del morsel['domain']
        # else set cookie to rewritten path
        if morsel.get('path'):
            del morsel['path']

        return morsel


# =================================================================
class RootScopeCookieRewriter(WbUrlBaseCookieRewriter):
    """
    Sometimes it is necessary to rewrite cookies to root scope
    in order to work across time boundaries and modifiers

    This rewriter simply sets all cookies to be in the root
    """

    def rewrite_cookie(self, name, morsel):
        # get root path
        morsel['path'] = self.url_rewriter.root_path

        # remove domain
        if morsel.get('domain'):
            del morsel['domain']

        return morsel


# =================================================================
def get_cookie_rewriter(cookie_scope):
    if cookie_scope == 'root':
        return RootScopeCookieRewriter
    elif cookie_scope == 'exact':
        return ExactPathCookieRewriter
    elif cookie_scope == 'host':
        return HostScopeCookieRewriter
    elif cookie_scope == 'removeall':
        return RemoveAllCookiesRewriter
    elif cookie_scope == 'coll':
        return MinimalScopeCookieRewriter
    else:
        return HostScopeCookieRewriter


# end pywb.rewrite.cookie_rewriter

# begin pywb.rewrite.header_rewriter

# =================================================================
class RewrittenStatusAndHeaders(object):
    def __init__(self, statusline, headers,
                 removed_header_dict, text_type, charset):
        self.status_headers = StatusAndHeaders(statusline, headers)
        self.removed_header_dict = removed_header_dict
        self.text_type = text_type
        self.charset = charset

    def contains_removed_header(self, name, value):
        return self.removed_header_dict.get(name) == value


# =================================================================
class HeaderRewriter(object):
    REWRITE_TYPES = {
        'html': ['text/html',
                 'application/xhtml',
                 'application/xhtml+xml'],

        'css': ['text/css'],

        'js': ['text/javascript',
               'application/javascript',
               'application/x-javascript'],

        'json': ['application/json'],

        'xml': ['/xml', '+xml', '.xml', '.rss'],
    }

    PROXY_HEADERS = ['content-type', 'content-disposition', 'content-range',
                     'accept-ranges']

    URL_REWRITE_HEADERS = ['location', 'content-location', 'content-base']

    ENCODING_HEADERS = ['content-encoding']

    REMOVE_HEADERS = ['transfer-encoding', 'content-security-policy',
                      'strict-transport-security']

    PROXY_NO_REWRITE_HEADERS = ['content-length']

    COOKIE_HEADERS = ['set-cookie', 'cookie']

    CACHE_HEADERS = ['cache-control', 'expires', 'etag', 'last-modified']

    def __init__(self, header_prefix='X-Archive-Orig-'):
        self.header_prefix = header_prefix

    def rewrite(self, status_headers, urlrewriter, cookie_rewriter):
        content_type = status_headers.get_header('Content-Type')
        text_type = None
        charset = None
        strip_encoding = False
        http_cache = None
        if urlrewriter:
            http_cache = urlrewriter.rewrite_opts.get('http_cache')

        if content_type:
            text_type = self._extract_text_type(content_type)
            if text_type:
                charset = self._extract_char_set(content_type)
                strip_encoding = True

        result = self._rewrite_headers(status_headers.headers,
                                       urlrewriter,
                                       cookie_rewriter,
                                       strip_encoding,
                                       http_cache)

        new_headers = result[0]
        removed_header_dict = result[1]

        if http_cache is not None and http_cache != 'pass':
            self._add_cache_headers(new_headers, http_cache)

        return RewrittenStatusAndHeaders(status_headers.statusline,
                                         new_headers,
                                         removed_header_dict,
                                         text_type,
                                         charset)

    def _add_cache_headers(self, new_headers, http_cache):
        try:
            age = int(http_cache)
        except:
            age = 0

        if age <= 0:
            new_headers.append(('Cache-Control', 'no-cache; no-store'))
        else:
            dt = datetime.utcnow()
            dt = dt + timedelta(seconds=age)
            new_headers.append(('Cache-Control', 'max-age=' + str(age)))
            new_headers.append(('Expires', datetime_to_http_date(dt)))

    def _extract_text_type(self, content_type):
        for ctype, mimelist in six.iteritems(self.REWRITE_TYPES):
            if any((mime in content_type) for mime in mimelist):
                return ctype

        return None

    def _extract_char_set(self, content_type):
        CHARSET_TOKEN = 'charset='
        idx = content_type.find(CHARSET_TOKEN)
        if idx < 0:
            return None

        return content_type[idx + len(CHARSET_TOKEN):].lower()

    def _rewrite_headers(self, headers, urlrewriter,
                         cookie_rewriter,
                         content_rewritten,
                         http_cache):

        new_headers = []
        removed_header_dict = {}

        def add_header(name, value):
            new_headers.append((name, value))

        def add_prefixed_header(name, value):
            new_headers.append((self.header_prefix + name, value))

        for (name, value) in headers:
            lowername = name.lower()

            if lowername in self.PROXY_HEADERS:
                add_header(name, value)

            elif urlrewriter and lowername in self.URL_REWRITE_HEADERS:
                new_headers.append((name, urlrewriter.rewrite(value)))

            elif lowername in self.ENCODING_HEADERS:
                if content_rewritten:
                    removed_header_dict[lowername] = value
                else:
                    add_header(name, value)

            elif lowername in self.REMOVE_HEADERS:
                removed_header_dict[lowername] = value
                add_prefixed_header(name, value)

            elif (lowername in self.PROXY_NO_REWRITE_HEADERS and
                      not content_rewritten):
                add_header(name, value)

            elif (lowername in self.COOKIE_HEADERS and
                      cookie_rewriter):
                cookie_list = cookie_rewriter.rewrite(value)
                new_headers.extend(cookie_list)

            elif (lowername in self.CACHE_HEADERS):
                if http_cache == 'pass':
                    add_header(name, value)
                else:
                    add_prefixed_header(name, value)

            elif urlrewriter:
                add_prefixed_header(name, value)
            else:
                add_header(name, value)

        return (new_headers, removed_header_dict)


# end  pywb.rewrite.header_rewriter

# begin pywb.rewrite.url_rewriter
# =================================================================
class UrlRewriter(object):
    """
    Main pywb UrlRewriter which rewrites absolute and relative urls
    to be relative to the current page, as specified via a WbUrl
    instance and an optional full path prefix
    """

    NO_REWRITE_URI_PREFIX = ('#', 'javascript:', 'data:',
                             'mailto:', 'about:', 'file:', '{')

    PROTOCOLS = ('http:', 'https:', 'ftp:', 'mms:', 'rtsp:', 'wais:')

    REL_SCHEME = ('//', r'\/\/', r'\\/\\/')

    def __init__(self, wburl, prefix='', full_prefix=None, rel_prefix=None,
                 root_path=None, cookie_scope=None, rewrite_opts=None):
        self.wburl = wburl if isinstance(wburl, WbUrl) else WbUrl(wburl)
        self.prefix = prefix
        self.full_prefix = full_prefix or prefix
        self.rel_prefix = rel_prefix or prefix
        self.root_path = root_path or '/'
        if self.full_prefix and self.full_prefix.startswith(self.PROTOCOLS):
            self.prefix_scheme = self.full_prefix.split(':')[0]
        else:
            self.prefix_scheme = None
        self.prefix_abs = self.prefix and self.prefix.startswith(self.PROTOCOLS)
        self.cookie_scope = cookie_scope
        self.rewrite_opts = rewrite_opts or {}

        if self.rewrite_opts.get('punycode_links'):
            self.wburl._do_percent_encode = False

    def rewrite(self, url, mod=None):
        # if special protocol, no rewriting at all
        if url.startswith(self.NO_REWRITE_URI_PREFIX):
            return url

        if (self.prefix and
                    self.prefix != '/' and
                url.startswith(self.prefix)):
            return url

        if (self.full_prefix and
                    self.full_prefix != self.prefix and
                url.startswith(self.full_prefix)):
            return url

        wburl = self.wburl

        is_abs = url.startswith(self.PROTOCOLS)

        scheme_rel = False
        if url.startswith(self.REL_SCHEME):
            is_abs = True
            scheme_rel = True
            # if prefix starts with a scheme
            # if self.prefix_scheme:
            #    url = self.prefix_scheme + ':' + url
            # url = 'http:' + url

        # optimize: join if not absolute url, otherwise just use as is
        if not is_abs:
            new_url = self.urljoin(wburl.url, url)
        else:
            new_url = url

        if mod is None:
            mod = wburl.mod

        final_url = self.prefix + wburl.to_str(mod=mod, url=new_url)

        if not is_abs and self.prefix_abs and not self.rewrite_opts.get('no_match_rel'):
            parts = final_url.split('/', 3)
            final_url = '/'
            if len(parts) == 4:
                final_url += parts[3]

        # experiment for setting scheme rel url
        elif scheme_rel and self.prefix_abs:
            final_url = final_url.split(':', 1)[1]

        return final_url

    def get_new_url(self, **kwargs):
        return self.prefix + self.wburl.to_str(**kwargs)

    def rebase_rewriter(self, new_url):
        if new_url.startswith(self.prefix):
            new_url = new_url[len(self.prefix):]
        elif new_url.startswith(self.rel_prefix):
            new_url = new_url[len(self.rel_prefix):]

        new_wburl = WbUrl(new_url)
        return self._create_rebased_rewriter(new_wburl, self.prefix)

    def _create_rebased_rewriter(self, new_wburl, prefix):
        return UrlRewriter(new_wburl, prefix)

    def get_cookie_rewriter(self, scope=None):
        # collection scope overrides rule scope?
        if self.cookie_scope:
            scope = self.cookie_scope

        cls = get_cookie_rewriter(scope)
        return cls(self)

    def deprefix_url(self):
        return self.wburl.deprefix_url(self.full_prefix)

    def __repr__(self):
        return "UrlRewriter('{0}', '{1}')".format(self.wburl, self.prefix)

    @staticmethod
    def urljoin(orig_url, url):  # pragma: no cover
        new_url = urljoin(orig_url, url)
        if '../' not in new_url:
            return new_url

        # only needed in py2 as py3 urljoin resolves '../'
        parts = urlsplit(new_url)
        scheme, netloc, path, query, frag = parts

        path_parts = path.split('/')
        i = 0
        n = len(path_parts) - 1
        while i < n:
            if path_parts[i] == '..':
                del path_parts[i]
                n -= 1
                if i > 0:
                    del path_parts[i - 1]
                    n -= 1
                    i -= 1
            else:
                i += 1

        if path_parts == ['']:
            path = '/'
        else:
            path = '/'.join(path_parts)

        parts = (scheme, netloc, path, query, frag)

        new_url = urlunsplit(parts)
        return new_url


# =================================================================
class SchemeOnlyUrlRewriter(UrlRewriter):
    """
    A url rewriter which ensures that any urls have the same
    scheme (http or https) as the base url.
    Other urls/input is unchanged.
    """

    def __init__(self, *args, **kwargs):
        super(SchemeOnlyUrlRewriter, self).__init__(*args, **kwargs)
        self.url_scheme = self.wburl.url.split(':')[0]
        if self.url_scheme == 'https':
            self.opposite_scheme = 'http'
        else:
            self.opposite_scheme = 'https'

    def rewrite(self, url, mod=None):
        if url.startswith(self.opposite_scheme + '://'):
            url = self.url_scheme + url[len(self.opposite_scheme):]

        return url

    def get_new_url(self, **kwargs):
        return kwargs.get('url', self.wburl.url)

    def rebase_rewriter(self, new_url):
        return self

    def get_cookie_rewriter(self, scope=None):
        return None

    def deprefix_url(self):
        return self.wburl.url


# end pywb.rewrite.url_rewriter

# being pywb.rewrite.regex_rewriters

# =================================================================
class RegexRewriter(object):
    # @staticmethod
    # def comment_out(string):
    #    return '/*' + string + '*/'

    @staticmethod
    def format(template):
        return lambda string: template.format(string)

    @staticmethod
    def remove_https(string):
        return string.replace("https", "http")

    @staticmethod
    def add_prefix(prefix):
        return lambda string: prefix + string

    @staticmethod
    def archival_rewrite(rewriter):
        return lambda string: rewriter.rewrite(string)

    # @staticmethod
    # def replacer(other):
    #    return lambda m, string: other

    HTTPX_MATCH_STR = r'https?:\\?/\\?/[A-Za-z0-9:_@.-]+'

    # DEFAULT_OP = add_prefix

    def __init__(self, rewriter, rules):
        # rules = self.create_rules(http_prefix)

        # Build regexstr, concatenating regex list
        regex_str = '|'.join(['(' + rx + ')' for rx, op, count in rules])

        # ensure it's not middle of a word, wrap in non-capture group
        regex_str = '(?<!\w)(?:' + regex_str + ')'

        self.regex = re.compile(regex_str, re.M)
        self.rules = rules

    def filter(self, m):
        return True

    def rewrite(self, string):
        return self.regex.sub(lambda x: self.replace(x), string)

    def close(self):
        return ''

    def replace(self, m):
        i = 0
        for _, op, count in self.rules:
            i += 1

            full_m = i
            while count > 0:
                i += 1
                count -= 1

            if not m.group(i):
                continue

            # Optional filter to skip matches
            if not self.filter(m):
                return m.group(0)

            # Custom func
            # if not hasattr(op, '__call__'):
            #    op = RegexRewriter.DEFAULT_OP(op)

            result = op(m.group(i))
            final_str = result

            # if extracting partial match
            if i != full_m:
                final_str = m.string[m.start(full_m):m.start(i)]
                final_str += result
                final_str += m.string[m.end(i):m.end(full_m)]

            return final_str

    @staticmethod
    def parse_rules_from_config(config):
        def run_parse_rules(rewriter):
            def parse_rule(obj):
                match = obj.get('match')
                if 'rewrite' in obj:
                    replace = RegexRewriter.archival_rewrite(rewriter)
                else:
                    replace = RegexRewriter.format(obj.get('replace', '{0}'))
                group = obj.get('group', 0)
                result = (match, replace, group)
                return result

            return list(map(parse_rule, config))

        return run_parse_rules


# =================================================================
class JSLinkRewriterMixin(object):
    """
    JS Rewriter which rewrites absolute http://, https:// and // urls
    at the beginning of a string
    """
    # JS_HTTPX = r'(?:(?:(?<=["\';])https?:)|(?<=["\']))\\{0,4}/\\{0,4}/[A-Za-z0-9:_@.-]+.*(?=["\s\';&\\])'
    # JS_HTTPX = r'(?<=["\';])(?:https?:)?\\{0,4}/\\{0,4}/[A-Za-z0-9:_@.\-/\\?&#]+(?=["\';&\\])'

    # JS_HTTPX = r'(?:(?<=["\';])https?:|(?<=["\']))\\{0,4}/\\{0,4}/[A-Za-z0-9:_@.-][^"\s\';&\\]*(?=["\';&\\])'
    JS_HTTPX = r'(?:(?<=["\';])https?:|(?<=["\']))\\{0,4}/\\{0,4}/[A-Za-z0-9:_@%.\\-]+/'

    def __init__(self, rewriter, rules=[]):
        rules = rules + [
            (self.JS_HTTPX, RegexRewriter.archival_rewrite(rewriter), 0)
        ]
        super(JSLinkRewriterMixin, self).__init__(rewriter, rules)


# =================================================================
class JSLocationRewriterMixin(object):
    """
    JS Rewriter mixin which rewrites location and domain to the
    specified prefix (default: 'WB_wombat_')
    """

    def __init__(self, rewriter, rules=[], prefix='WB_wombat_'):
        rules = rules + [
            #  (r'(?<![/$])\blocation\b(?!\":)', RegexRewriter.add_prefix(prefix), 0),
            (r'(?<![/$\'"-])\b(?:location|top)\b(?!(?:\":|:|=\d|-))', RegexRewriter.add_prefix(prefix), 0),

            (r'(?<=\.)postMessage\b\(', RegexRewriter.add_prefix('__WB_pmw(window).'), 0),

            (r'(?<=\.)frameElement\b', RegexRewriter.add_prefix(prefix), 0),
            #  (r'(?<=document\.)domain', RegexRewriter.add_prefix(prefix), 0),
            #  (r'(?<=document\.)referrer', RegexRewriter.add_prefix(prefix), 0),
            #  (r'(?<=document\.)cookie', RegexRewriter.add_prefix(prefix), 0),

            # todo: move to mixin?
            # (r'(?<=[\s=(){])(top)\s*(?:[!}?)]|==|$)',
            # (r'(?<=[\s=(){.])(top)\s*(?:[,!}?)]|==|$)',
            #  RegexRewriter.add_prefix(prefix), 1),

            # (r'^(top)\s*(?:[!})]|==|$)',
            #  RegexRewriter.add_prefix(prefix), 1),

            # (r'(?<=window\.)(top)',
            #  RegexRewriter.add_prefix(prefix), 1),
        ]
        super(JSLocationRewriterMixin, self).__init__(rewriter, rules)


# =================================================================
class JSLocationOnlyRewriter(JSLocationRewriterMixin, RegexRewriter):
    pass


# =================================================================
class JSLinkOnlyRewriter(JSLinkRewriterMixin, RegexRewriter):
    pass


# =================================================================
class JSLinkAndLocationRewriter(JSLocationRewriterMixin,
                                JSLinkRewriterMixin,
                                RegexRewriter):
    pass


# =================================================================
class JSNoneRewriter(RegexRewriter):
    def __init__(self, rewriter, rules=[]):
        super(JSNoneRewriter, self).__init__(rewriter, rules)


# =================================================================
# Set 'default' JSRewriter
JSRewriter = JSLinkAndLocationRewriter


# =================================================================
class XMLRewriter(RegexRewriter):
    def __init__(self, rewriter, extra=[]):
        rules = self._create_rules(rewriter)

        super(XMLRewriter, self).__init__(rewriter, rules)

    # custom filter to reject 'xmlns' attr
    def filter(self, m):
        attr = m.group(1)
        if attr and attr.startswith('xmlns'):
            return False

        return True

    def _create_rules(self, rewriter):
        return [
            ('([A-Za-z:]+[\s=]+)?["\'\s]*(' +
             RegexRewriter.HTTPX_MATCH_STR + ')',
             RegexRewriter.archival_rewrite(rewriter), 2),
        ]


# =================================================================
class CSSRewriter(RegexRewriter):
    CSS_URL_REGEX = "url\\s*\\(\\s*[\\\\\"']*([^)'\"]+)[\\\\\"']*\\s*\\)"

    CSS_IMPORT_NO_URL_REGEX = ("@import\\s+(?!url)\\(?\\s*['\"]?" +
                               "(?!url[\\s\\(])([\w.:/\\\\-]+)")

    def __init__(self, rewriter):
        rules = self._create_rules(rewriter)
        super(CSSRewriter, self).__init__(rewriter, rules)

    def _create_rules(self, rewriter):
        return [
            (CSSRewriter.CSS_URL_REGEX,
             RegexRewriter.archival_rewrite(rewriter), 1),

            (CSSRewriter.CSS_IMPORT_NO_URL_REGEX,
             RegexRewriter.archival_rewrite(rewriter), 1),
        ]


# end pywb.rewrite.regex_rewriters


# begin pywb.rewrite.html_rewriter
# =================================================================
class HTMLRewriterMixin(object):
    """
    HTML-Parsing Rewriter for custom rewriting, also delegates
    to rewriters for script and css
    """

    @staticmethod
    def _init_rewrite_tags(defmod):
        rewrite_tags = {
            'a': {'href': defmod},
            'applet': {'codebase': 'oe_',
                       'archive': 'oe_'},
            'area': {'href': defmod},
            'audio': {'src': 'oe_'},
            'base': {'href': defmod},
            'blockquote': {'cite': defmod},
            'body': {'background': 'im_'},
            'button': {'formaction': defmod},
            'command': {'icon': 'im_'},
            'del': {'cite': defmod},
            'embed': {'src': 'oe_'},
            'head': {'': defmod},  # for head rewriting
            'iframe': {'src': 'if_'},
            'img': {'src': 'im_',
                    'srcset': 'im_'},
            'ins': {'cite': defmod},
            'input': {'src': 'im_',
                      'formaction': defmod},
            'form': {'action': defmod},
            'frame': {'src': 'fr_'},
            'link': {'href': 'oe_'},
            'meta': {'content': defmod},
            'object': {'codebase': 'oe_',
                       'data': 'oe_'},
            'param': {'value': 'oe_'},
            'q': {'cite': defmod},
            'ref': {'href': 'oe_'},
            'script': {'src': 'js_'},
            'source': {'src': 'oe_'},
            'video': {'src': 'oe_',
                      'poster': 'im_'},
        }

        return rewrite_tags

    STATE_TAGS = ['script', 'style']

    # tags allowed in the <head> of an html document
    HEAD_TAGS = ['html', 'head', 'base', 'link', 'meta',
                 'title', 'style', 'script', 'object', 'bgsound']

    BEFORE_HEAD_TAGS = ['html', 'head']

    DATA_RW_PROTOCOLS = ('http://', 'https://', '//')

    # ===========================
    class AccumBuff:
        def __init__(self):
            self.ls = []

        def write(self, string):
            self.ls.append(string)

        def getvalue(self):
            return ''.join(self.ls)

    # ===========================
    def __init__(self, url_rewriter,
                 head_insert=None,
                 js_rewriter_class=JSRewriter,
                 css_rewriter_class=CSSRewriter,
                 url='',
                 defmod='',
                 parse_comments=False):

        self.url_rewriter = url_rewriter
        self._wb_parse_context = None

        self.js_rewriter = js_rewriter_class(url_rewriter)
        self.css_rewriter = css_rewriter_class(url_rewriter)

        self.head_insert = head_insert
        self.parse_comments = parse_comments

        self.orig_url = url
        self.defmod = defmod
        self.rewrite_tags = self._init_rewrite_tags(defmod)

        # get opts from urlrewriter
        self.opts = url_rewriter.rewrite_opts

        self.force_decl = self.opts.get('force_html_decl', None)

        self.parsed_any = False
        self.has_base = False

    # ===========================
    META_REFRESH_REGEX = re.compile('^[\\d.]+\\s*;\\s*url\\s*=\\s*(.+?)\\s*$',
                                    re.IGNORECASE | re.MULTILINE)

    def _rewrite_meta_refresh(self, meta_refresh):
        if not meta_refresh:
            return ''

        m = self.META_REFRESH_REGEX.match(meta_refresh)
        if not m:
            return meta_refresh

        meta_refresh = (meta_refresh[:m.start(1)] +
                        self._rewrite_url(m.group(1)) +
                        meta_refresh[m.end(1):])

        return meta_refresh

    def _rewrite_base(self, url, mod=''):
        if not url:
            return ''

        url = self._ensure_url_has_path(url)

        base_url = self._rewrite_url(url, mod)

        self.url_rewriter = (self.url_rewriter.
                             rebase_rewriter(base_url))
        self.has_base = True

        if self.opts.get('rewrite_base', True):
            return base_url
        else:
            return url

    def _write_default_base(self):
        if not self.orig_url:
            return

        base_url = self._ensure_url_has_path(self.orig_url)

        # write default base only if different from implicit base
        if self.orig_url != base_url:
            base_url = self._rewrite_url(base_url)
            self.out.write('<base href="{0}"/>'.format(base_url))

        self.has_base = True

    def _ensure_url_has_path(self, url):
        """ ensure the url has a path component
        eg. http://example.com#abc converted to http://example.com/#abc
        """
        inx = url.find('://')
        if inx > 0:
            rest = url[inx + 3:]
        elif url.startswith('//'):
            rest = url[2:]
        else:
            rest = url

        if '/' in rest:
            return url

        scheme, netloc, path, query, frag = urlsplit(url)
        if not path:
            path = '/'

        url = urlunsplit((scheme, netloc, path, query, frag))
        return url

    def _rewrite_url(self, value, mod=None):
        if not value:
            return ''

        value = value.strip()
        if not value:
            return ''

        value = self.try_unescape(value)
        return self.url_rewriter.rewrite(value, mod)

    def try_unescape(self, value):
        if not value.startswith('http'):
            return value

        try:
            new_value = HTMLParser.unescape(self, value)
        except:
            return value

        if value != new_value:
            # ensure utf-8 encoded to avoid %-encoding query here
            if isinstance(new_value, text_type):
                new_value = new_value.encode('utf-8')

        return new_value

    def _rewrite_srcset(self, value, mod=''):
        if not value:
            return ''

        values = value.split(',')
        values = [self._rewrite_url(v.strip()) for v in values]
        return ', '.join(values)

    def _rewrite_css(self, css_content):
        if css_content:
            return self.css_rewriter.rewrite(css_content)
        else:
            return ''

    def _rewrite_script(self, script_content):
        if script_content:
            return self.js_rewriter.rewrite(script_content)
        else:
            return ''

    def has_attr(self, tag_attrs, attr):
        name, value = attr
        for attr_name, attr_value in tag_attrs:
            if attr_name == name:
                return value.lower() == attr_value.lower()
        return False

    def _rewrite_tag_attrs(self, tag, tag_attrs):
        # special case: head insertion, before-head tags
        if (self.head_insert and
                not self._wb_parse_context
            and (tag not in self.BEFORE_HEAD_TAGS)):
            self.out.write(self.head_insert)
            self.head_insert = None

        # special case: script or style parse context
        if ((tag in self.STATE_TAGS) and not self._wb_parse_context):
            self._wb_parse_context = tag

        # attr rewriting
        handler = self.rewrite_tags.get(tag)
        if not handler:
            handler = {}

        self.out.write('<' + tag)

        for attr_name, attr_value in tag_attrs:
            empty_attr = False
            if attr_value is None:
                attr_value = ''
                empty_attr = True

            # special case: inline JS/event handler
            if ((attr_value and attr_value.startswith('javascript:'))
                or attr_name.startswith('on')):
                attr_value = self._rewrite_script(attr_value)

            # special case: inline CSS/style attribute
            elif attr_name == 'style':
                attr_value = self._rewrite_css(attr_value)

            # special case: deprecated background attribute
            elif attr_name == 'background':
                rw_mod = 'im_'
                attr_value = self._rewrite_url(attr_value, rw_mod)

            # special case: srcset list
            elif attr_name == 'srcset':
                rw_mod = handler.get(attr_name, '')
                attr_value = self._rewrite_srcset(attr_value, rw_mod)

            # special case: disable crossorigin and integrity attr
            # as they may interfere with rewriting semantics
            elif attr_name in ('crossorigin', 'integrity'):
                attr_name = '_' + attr_name

            # special case: if rewrite_canon not set,
            # don't rewrite rel=canonical
            elif tag == 'link' and attr_name == 'href':
                rw_mod = handler.get(attr_name)

                if self.has_attr(tag_attrs, ('rel', 'canonical')):
                    if self.opts.get('rewrite_rel_canon', True):
                        attr_value = self._rewrite_url(attr_value, rw_mod)
                    else:
                        # resolve relative rel=canonical URLs so that they
                        # refer to the same absolute URL as on the original
                        # page (see https://github.com/hypothesis/via/issues/65
                        # for context)
                        attr_value = urljoin(self.orig_url, attr_value)
                else:
                    attr_value = self._rewrite_url(attr_value, rw_mod)

            # special case: meta tag
            elif (tag == 'meta') and (attr_name == 'content'):
                if self.has_attr(tag_attrs, ('http-equiv', 'refresh')):
                    attr_value = self._rewrite_meta_refresh(attr_value)
                elif attr_value.startswith(self.DATA_RW_PROTOCOLS):
                    rw_mod = handler.get(attr_name)
                    attr_value = self._rewrite_url(attr_value, rw_mod)

            # special case: param value, conditional rewrite
            elif (tag == 'param'):
                if attr_value.startswith(self.DATA_RW_PROTOCOLS):
                    rw_mod = handler.get(attr_name)
                    attr_value = self._rewrite_url(attr_value, rw_mod)

            # special case: data- attrs, conditional rewrite
            elif attr_name and attr_value and attr_name.startswith('data-'):
                if attr_value.startswith(self.DATA_RW_PROTOCOLS):
                    rw_mod = 'oe_'
                    attr_value = self._rewrite_url(attr_value, rw_mod)

            # special case: base tag
            elif (tag == 'base') and (attr_name == 'href') and attr_value:
                rw_mod = handler.get(attr_name)
                attr_value = self._rewrite_base(attr_value, rw_mod)
            else:
                # rewrite url using tag handler
                rw_mod = handler.get(attr_name)
                if rw_mod is not None:
                    attr_value = self._rewrite_url(attr_value, rw_mod)

            # write the attr!
            self._write_attr(attr_name, attr_value, empty_attr)

        return True

    def _rewrite_head(self, start_end):
        # special case: head tag

        # if no insert or in context, no rewrite
        if not self.head_insert or self._wb_parse_context:
            return False

        self.out.write('>')
        self.out.write(self.head_insert)
        self.head_insert = None

        if start_end:
            if not self.has_base:
                self._write_default_base()

            self.out.write('</head>')

        return True

    def _write_attr(self, name, value, empty_attr):
        # if empty_attr is set, just write 'attr'!
        if empty_attr:
            self.out.write(' ' + name)

        # write with value, if set
        elif value:

            self.out.write(' ' + name + '="' + value.replace('"', '&quot;') + '"')

        # otherwise, 'attr=""' is more common, so use that form
        else:
            self.out.write(' ' + name + '=""')

    def parse_data(self, data):
        if self._wb_parse_context == 'script':
            data = self._rewrite_script(data)
        elif self._wb_parse_context == 'style':
            data = self._rewrite_css(data)

        self.out.write(data)

    def rewrite(self, string):
        self.out = self.AccumBuff()

        self.feed(string)

        result = self.out.getvalue()

        # track that something was parsed
        self.parsed_any = self.parsed_any or bool(string)

        # Clear buffer to create new one for next rewrite()
        self.out = None

        if self.force_decl:
            result = self.force_decl + '\n' + result
            self.force_decl = None

        return result

    def close(self):
        self.out = self.AccumBuff()

        self._internal_close()

        result = self.out.getvalue()

        # Clear buffer to create new one for next rewrite()
        self.out = None

        return result

    def _internal_close(self):  # pragma: no cover
        raise NotImplementedError('Base method')


# =================================================================
class HTMLRewriter(HTMLRewriterMixin, HTMLParser):
    PARSETAG = re.compile('[<]')

    def __init__(self, *args, **kwargs):
        if sys.version_info > (3, 4):  # pragma: no cover
            HTMLParser.__init__(self, convert_charrefs=False)
        else:  # pragma: no cover
            HTMLParser.__init__(self)

        super(HTMLRewriter, self).__init__(*args, **kwargs)

    def reset(self):
        HTMLParser.reset(self)
        self.interesting = self.PARSETAG

    def clear_cdata_mode(self):
        HTMLParser.clear_cdata_mode(self)
        self.interesting = self.PARSETAG

    def feed(self, string):
        try:
            HTMLParser.feed(self, string)
        except Exception as e:  # pragma: no cover
            import traceback
            traceback.print_exc()
            self.out.write(string)

    def _internal_close(self):
        if (self._wb_parse_context):
            end_tag = '</' + self._wb_parse_context + '>'
            self.feed(end_tag)
            self._wb_parse_context = None

        # if haven't insert head_insert, but wrote some content
        # out, then insert head_insert now
        if self.head_insert and self.parsed_any:
            self.out.write(self.head_insert)
            self.head_insert = None

        try:
            HTMLParser.close(self)
        except Exception:  # pragma: no cover
            # only raised in 2.6
            pass

    # called to unescape attrs -- do not unescape!
    def unescape(self, s):
        return s

    def handle_starttag(self, tag, attrs):
        self._rewrite_tag_attrs(tag, attrs)

        if tag != 'head' or not self._rewrite_head(False):
            self.out.write('>')

    def handle_startendtag(self, tag, attrs):
        self._rewrite_tag_attrs(tag, attrs)

        if tag != 'head' or not self._rewrite_head(True):
            self.out.write('/>')

    def handle_endtag(self, tag):
        if (tag == self._wb_parse_context):
            self._wb_parse_context = None

        if tag == 'head' and not self.has_base:
            self._write_default_base()

        self.out.write('</' + tag + '>')

    def handle_data(self, data):
        self.parse_data(data)

    # overriding regex so that these are no longer called
    # def handle_entityref(self, data):
    #    self.out.write('&' + data + ';')

    # def handle_charref(self, data):
    #    self.out.write('&#' + data + ';')

    def handle_comment(self, data):
        self.out.write('<!--')
        if self.parse_comments:
            # data = self._rewrite_script(data)

            # Rewrite with seperate HTMLRewriter
            comment_rewriter = HTMLRewriter(self.url_rewriter,
                                            defmod=self.defmod)

            data = comment_rewriter.rewrite(data)
            data += comment_rewriter.close()
            self.out.write(data)
        else:
            self.parse_data(data)
        self.out.write('-->')

    def handle_decl(self, data):
        self.out.write('<!' + data + '>')
        self.force_decl = None

    def handle_pi(self, data):
        self.out.write('<?' + data + '>')

    def unknown_decl(self, data):
        self.out.write('<![')
        self.parse_data(data)
        self.out.write(']>')


# end pywb.rewrite.html_rewriter

# begin pywb.rewrite.rewriterules
# =================================================================
class RewriteRules(BaseRule):
    def __init__(self, url_prefix, config={}):
        super(RewriteRules, self).__init__(url_prefix, config)

        self.rewriters = {}

        # self._script_head_inserts = config.get('script_head_inserts', {})

        self.rewriters['header'] = config.get('header_class', HeaderRewriter)
        self.rewriters['css'] = config.get('css_class', CSSRewriter)
        self.rewriters['xml'] = config.get('xml_class', XMLRewriter)
        self.rewriters['html'] = config.get('html_class', HTMLRewriter)
        self.rewriters['json'] = config.get('json_class', JSLinkOnlyRewriter)

        self.parse_comments = config.get('parse_comments', False)

        # Custom handling for js rewriting, often the most complex
        self.js_rewrite_location = config.get('js_rewrite_location', 'location')

        # ability to toggle rewriting
        if self.js_rewrite_location == 'all':
            js_default_class = JSLinkAndLocationRewriter
        elif self.js_rewrite_location == 'location':
            js_default_class = JSLocationOnlyRewriter
            self.rewriters['json'] = JSNoneRewriter
        elif self.js_rewrite_location == 'none':
            js_default_class = JSNoneRewriter
            self.rewriters['json'] = JSNoneRewriter
        else:
            js_default_class = JSLinkOnlyRewriter

        # set js class, using either default or override from config
        self.rewriters['js'] = config.get('js_class', js_default_class)

        # add any regexs for js rewriter
        self._add_custom_regexs('js', config)

        # cookie rewrite scope
        self.cookie_scope = config.get('cookie_scope', 'default')

        req_cookie_rewrite = config.get('req_cookie_rewrite', [])
        for rc in req_cookie_rewrite:
            rc['rx'] = re.compile(rc.get('match', ''))

        self.req_cookie_rewrite = req_cookie_rewrite

    def _add_custom_regexs(self, field, config):
        regexs = config.get(field + '_regexs')
        if not regexs:
            return

        rewriter_cls = self.rewriters[field]

        # rule_def_tuples = RegexRewriter.parse_rules_from_config(regexs)
        parse_rules_func = RegexRewriter.parse_rules_from_config(regexs)

        def extend_rewriter_with_regex(urlrewriter):
            rule_def_tuples = parse_rules_func(urlrewriter)
            return rewriter_cls(urlrewriter, rule_def_tuples)

        self.rewriters[field] = extend_rewriter_with_regex


# end pywb.rewrite.rewriterules

# begin pywb.rewrite.rewrite_content
# =================================================================
class RewriteContent(object):
    HEAD_REGEX = re.compile(b'<\s*head\\b[^>]*[>]+', re.I)

    TAG_REGEX = re.compile(b'^\s*\<')

    CHARSET_REGEX = re.compile(b'<meta[^>]*?[\s;"\']charset\s*=[\s"\']*([^\s"\'/>]*)')

    BUFF_SIZE = 16384

    def __init__(self, ds_rules_file=None, is_framed_replay=False):
        self.ruleset = RuleSet(RewriteRules, 'rewrite',
                               default_rule_config={},
                               ds_rules_file=ds_rules_file)

        if is_framed_replay == 'inverse':
            self.defmod = 'mp_'
        else:
            self.defmod = ''

    def sanitize_content(self, status_headers, stream):
        # remove transfer encoding chunked and wrap in a dechunking stream
        if (status_headers.remove_header('transfer-encoding')):
            stream = ChunkedDataReader(stream)

        return (status_headers, stream)

    def _rewrite_headers(self, urlrewriter, rule, status_headers, stream,
                         urlkey='', cookie_rewriter=None):

        header_rewriter_class = rule.rewriters['header']

        if urlrewriter and not cookie_rewriter:
            cookie_rewriter = urlrewriter.get_cookie_rewriter(rule)

        rewritten_headers = (header_rewriter_class().
                             rewrite(status_headers,
                                     urlrewriter,
                                     cookie_rewriter))

        # note: since chunk encoding may/may not be valid,
        # the approach taken here is to *always* attempt
        # to dechunk if 'transfer-encoding: chunked' is present
        #
        # an alternative may be to serve chunked unless
        # content rewriting is needed
        # todo: possible revisit this approach

        if (rewritten_headers.
                    contains_removed_header('transfer-encoding', 'chunked')):
            stream = ChunkedDataReader(stream)

        return (rewritten_headers, stream)

    def _check_encoding(self, rewritten_headers, stream, enc):
        matched = False
        if (rewritten_headers.
                    contains_removed_header('content-encoding', enc)):

            # optimize: if already a ChunkedDataReader, add the encoding
            if isinstance(stream, ChunkedDataReader):
                stream.set_decomp(enc)
            else:
                stream = DecompressingBufferedReader(stream, decomp_type=enc)

            rewritten_headers.status_headers.remove_header('content-length')
            matched = True

        return matched, stream

    def rewrite_content(self, urlrewriter, status_headers, stream,
                        head_insert_func=None, urlkey='',
                        cdx=None, cookie_rewriter=None, env=None):

        wb_url = urlrewriter.wburl

        if (wb_url.is_identity or
                (not head_insert_func and wb_url.is_banner_only)):
            status_headers, stream = self.sanitize_content(status_headers,
                                                           stream)
            return (status_headers, self.stream_to_gen(stream), False)

        if urlrewriter and cdx and cdx.get('is_live'):
            urlrewriter.rewrite_opts['is_live'] = True

        rule = self.ruleset.get_first_match(urlkey)

        (rewritten_headers, stream) = self._rewrite_headers(urlrewriter,
                                                            rule,
                                                            status_headers,
                                                            stream,
                                                            urlkey,
                                                            cookie_rewriter)

        status_headers = rewritten_headers.status_headers

        res = self.handle_custom_rewrite(rewritten_headers.text_type,
                                         status_headers,
                                         stream,
                                         env)
        if res:
            return res

        # Handle text content rewriting
        # ====================================================================
        # special case -- need to ungzip the body

        text_type = rewritten_headers.text_type

        # see known js/css modifier specified, the context should run
        # default text_type
        mod = wb_url.mod

        stream_raw = False
        encoding = None
        first_buff = b''

        for decomp_type in BufferedReader.get_supported_decompressors():
            matched, stream = self._check_encoding(rewritten_headers,
                                                   stream,
                                                   decomp_type)
            if matched:
                break

        if mod == 'js_':
            text_type, stream = self._resolve_text_type('js',
                                                        text_type,
                                                        stream)
        elif mod == 'cs_':
            text_type, stream = self._resolve_text_type('css',
                                                        text_type,
                                                        stream)

        rewriter_class = rule.rewriters[text_type]

        # for html, need to perform header insert, supply js, css, xml
        # rewriters
        if text_type == 'html':
            head_insert_str = ''
            charset = rewritten_headers.charset

            # if no charset set, attempt to extract from first 1024
            if not rewritten_headers.charset:
                first_buff = stream.read(1024)
                charset = self._extract_html_charset(first_buff,
                                                     status_headers)

            if head_insert_func and not wb_url.is_url_rewrite_only:
                head_insert_orig = head_insert_func(rule, cdx)

                if charset:
                    try:
                        head_insert_str = webencodings.encode(head_insert_orig, charset)
                    except:
                        pass

                if not head_insert_str:
                    charset = 'utf-8'
                    head_insert_str = head_insert_orig.encode(charset)

                head_insert_buf = head_insert_str
                # head_insert_str = to_native_str(head_insert_str)
                head_insert_str = head_insert_str.decode('iso-8859-1')

            if wb_url.is_banner_only:
                gen = self._head_insert_only_gen(head_insert_buf,
                                                 stream,
                                                 first_buff)

                content_len = status_headers.get_header('Content-Length')
                try:
                    content_len = int(content_len)
                except Exception:
                    content_len = None

                if content_len and content_len >= 0:
                    content_len = str(content_len + len(head_insert_str))
                    status_headers.replace_header('Content-Length',
                                                  content_len)

                return (status_headers, gen, False)

            js_rewriter_class = rule.rewriters['js']
            css_rewriter_class = rule.rewriters['css']

            if wb_url.is_url_rewrite_only:
                js_rewriter_class = JSNoneRewriter

            rewriter = rewriter_class(urlrewriter,
                                      js_rewriter_class=js_rewriter_class,
                                      css_rewriter_class=css_rewriter_class,
                                      head_insert=head_insert_str,
                                      url=wb_url.url,
                                      defmod=self.defmod,
                                      parse_comments=rule.parse_comments)

        else:
            if wb_url.is_banner_only:
                return (status_headers, self.stream_to_gen(stream), False)

            # url-only rewriter, but not rewriting urls in JS, so return
            if wb_url.is_url_rewrite_only and text_type == 'js':
                # return (status_headers, self.stream_to_gen(stream), False)
                rewriter_class = JSLinkOnlyRewriter

            # apply one of (js, css, xml) rewriters
            rewriter = rewriter_class(urlrewriter)

        # align to line end for all non-html rewriting
        align = (text_type != 'html')

        # Create rewriting generator
        gen = self.rewrite_text_stream_to_gen(stream,
                                              rewrite_func=rewriter.rewrite,
                                              final_read_func=rewriter.close,
                                              first_buff=first_buff,
                                              align_to_line=align)

        return (status_headers, gen, True)

    def handle_custom_rewrite(self, text_type, status_headers, stream, env):
        # use rewritten headers, but no further rewriting needed
        if text_type is None:
            return (status_headers, self.stream_to_gen(stream), False)

    @staticmethod
    def _extract_html_charset(buff, status_headers):
        charset = None
        m = RewriteContent.CHARSET_REGEX.search(buff)
        if m:
            charset = m.group(1)
            charset = to_native_str(charset)
        # content_type = 'text/html; charset=' + charset
        #    status_headers.replace_header('content-type', content_type)

        return charset

    @staticmethod
    def _resolve_text_type(mod, text_type, stream):
        if text_type == 'css' and mod == 'js':
            return 'css', stream

        # only attempt to resolve between html and other text types
        if text_type != 'html':
            return mod, stream

        buff = stream.read(128)

        wrapped_stream = BufferedReader(stream, starting_data=buff)

        # check if starts with a tag, then likely html
        if RewriteContent.TAG_REGEX.match(buff):
            mod = 'html'

        return mod, wrapped_stream

    def _head_insert_only_gen(self, insert_str, stream, first_buff=b''):
        buff = first_buff
        max_len = 1024 - len(first_buff)
        while max_len > 0:
            curr = stream.read(max_len)
            if not curr:
                break

            max_len -= len(buff)
            buff += curr

        matcher = self.HEAD_REGEX.search(buff)

        if matcher:
            yield buff[:matcher.end()]
            yield insert_str
            yield buff[matcher.end():]
        else:
            yield insert_str
            yield buff

        for buff in self.stream_to_gen(stream):
            yield buff

    @staticmethod
    def _decode_buff(buff, stream, encoding):  # pragma: no coverage
        try:
            buff = buff.decode(encoding)
        except UnicodeDecodeError as e:
            # chunk may have cut apart unicode bytes -- add 1-3 bytes and retry
            for i in range(3):
                buff += stream.read(1)
                try:
                    buff = buff.decode(encoding)
                    break
                except UnicodeDecodeError:
                    pass
            else:
                raise

        return buff

    @staticmethod
    def stream_to_gen(stream):
        """
        Convert stream to an iterator, reading BUFF_SIZE bytes
        """
        try:
            while True:
                buff = stream.read(RewriteContent.BUFF_SIZE)
                yield buff
                if not buff:
                    break

        finally:
            stream.close()

    @staticmethod
    def rewrite_text_stream_to_gen(stream, rewrite_func,
                                   final_read_func, first_buff,
                                   align_to_line):
        """
        Convert stream to generator using applying rewriting func
        to each portion of the stream.
        Align to line boundaries if needed.
        """
        try:
            has_closed = hasattr(stream, 'closed')
            buff = first_buff

            while True:
                if buff:
                    buff = rewrite_func(buff.decode('iso-8859-1'))
                    yield buff.encode('iso-8859-1')

                buff = stream.read(RewriteContent.BUFF_SIZE)
                # on 2.6, readline() (but not read()) throws an exception
                # if stream already closed, so check stream.closed if present
                if (buff and align_to_line and
                        (not has_closed or not stream.closed)):
                    buff += stream.readline()

                if not buff:
                    break

            # For adding a tail/handling final buffer
            buff = final_read_func()
            if buff:
                yield buff.encode('iso-8859-1')

        finally:
            stream.close()


# end pywb.rewrite.rewrite_content

# begin pywb.rewrite.rewrite_live
# =================================================================
class LiveRewriter(object):
    def __init__(self, is_framed_replay=False, proxies=None):
        self.rewriter = RewriteContent(is_framed_replay=is_framed_replay)

        self.proxies = proxies

        self.live_request = live_request

        if self.proxies:
            logging.debug('Live Rewrite via proxy ' + str(proxies))

            if isinstance(proxies, str):
                self.proxies = {'http': proxies,
                                'https': proxies}

        else:
            logging.debug('Live Rewrite Direct (no proxy)')

    def is_recording(self):
        return self.proxies is not None

    def fetch_local_file(self, uri):
        # fh = open(uri)
        fh = LocalFileLoader().load(uri)

        content_type, _ = mimetypes.guess_type(uri)

        # create fake headers for local file
        status_headers = StatusAndHeaders('200 OK',
                                          [('Content-Type', content_type)])
        stream = fh

        return (status_headers, stream)

    def translate_headers(self, url, urlkey, env):
        headers = {}

        splits = urlsplit(url)
        has_cookies = False

        for name, value in six.iteritems(env):
            if name == 'HTTP_HOST':
                name = 'Host'
                value = splits.netloc

            elif name == 'HTTP_ORIGIN':
                name = 'Origin'
                value = (splits.scheme + '://' + splits.netloc)

            elif name == 'HTTP_X_CSRFTOKEN':
                name = 'X-CSRFToken'
                cookie_val = extract_client_cookie(env, 'csrftoken')
                if cookie_val:
                    value = cookie_val

            elif name == 'HTTP_REFERER':
                continue

            elif name == 'HTTP_X_PYWB_REQUESTED_WITH':
                continue

            elif name == 'HTTP_X_FORWARDED_PROTO':
                name = 'X-Forwarded-Proto'
                value = splits.scheme

            elif name == 'HTTP_COOKIE':
                name = 'Cookie'
                value = self._req_cookie_rewrite(urlkey, value)
                has_cookies = True

            elif name.startswith('HTTP_'):
                name = name[5:].title().replace('_', '-')

            elif name in ('CONTENT_LENGTH', 'CONTENT_TYPE'):
                name = name.title().replace('_', '-')

            elif name == 'REL_REFERER':
                name = 'Referer'
            else:
                value = None

            if value:
                headers[name] = value

        if not has_cookies:
            value = self._req_cookie_rewrite(urlkey, '')
            if value:
                headers['Cookie'] = value

        return headers

    def _req_cookie_rewrite(self, urlkey, value):
        rule = self.rewriter.ruleset.get_first_match(urlkey)
        if not rule or not rule.req_cookie_rewrite:
            return value

        for cr in rule.req_cookie_rewrite:
            try:
                value = cr['rx'].sub(cr['replace'], value)
            except KeyError:
                pass

        return value

    def fetch_http(self, url,
                   urlkey=None,
                   env=None,
                   req_headers=None,
                   follow_redirects=False,
                   skip_recording=False,
                   verify=True):

        method = 'GET'
        data = None

        proxies = None
        if not skip_recording:
            proxies = self.proxies

        if not req_headers:
            req_headers = {}

        if env is not None:
            method = env['REQUEST_METHOD'].upper()
            input_ = env['wsgi.input']

            req_headers.update(self.translate_headers(url, urlkey, env))

            if method in ('POST', 'PUT'):
                len_ = env.get('CONTENT_LENGTH')
                if len_:
                    data = LimitReader(input_, int(len_))
                else:
                    data = input_

        response = self.live_request(method=method,
                                     url=url,
                                     data=data,
                                     headers=req_headers,
                                     allow_redirects=follow_redirects,
                                     proxies=proxies,
                                     stream=True,
                                     verify=verify)

        statusline = str(response.status_code) + ' ' + response.reason

        headers = response.headers.items()

        stream = response.raw

        try:  # pragma: no cover
            # PY 3
            headers = stream._original_response.headers._headers
        except:  # pragma: no cover
            # PY 2
            headers = []
            resp_headers = stream._original_response.msg.headers
            for h in resp_headers:
                n, v = h.split(':', 1)
                n = n.strip()
                v = v.strip()
                headers.append((n, v))

        status_headers = StatusAndHeaders(statusline, headers)

        return (status_headers, stream)

    def fetch_request(self, url, urlrewriter,
                      head_insert_func=None,
                      urlkey=None,
                      env=None,
                      req_headers={},
                      timestamp=None,
                      follow_redirects=False,
                      skip_recording=False,
                      verify=True,
                      remote_only=True):

        ts_err = url.split('///')

        # fixup for accidental erroneous rewrite which has ///
        # (unless file:///)
        if len(ts_err) > 1 and ts_err[0] != 'file:':
            url = 'http://' + ts_err[1]

        if url.startswith('//'):
            url = 'http:' + url

        if remote_only or is_http(url):
            is_remote = True
        else:
            is_remote = False
            if not url.startswith('file:'):
                url = to_file_url(url)

        # explicit urlkey may be passed in (say for testing)
        if not urlkey:
            urlkey = canonicalize(url)

        if is_remote:
            (status_headers, stream) = self.fetch_http(url, urlkey, env,
                                                       req_headers,
                                                       follow_redirects,
                                                       skip_recording,
                                                       verify)
        else:
            (status_headers, stream) = self.fetch_local_file(url)

        if timestamp is None:
            timestamp = timestamp_now()

        cdx = {'urlkey': urlkey,
               'timestamp': timestamp,
               'url': url,
               'status': status_headers.get_statuscode(),
               'mime': status_headers.get_header('Content-Type'),
               'is_live': True,
               }

        result = (self.rewriter.
                  rewrite_content(urlrewriter,
                                  status_headers,
                                  stream,
                                  head_insert_func=head_insert_func,
                                  urlkey=urlkey,
                                  cdx=cdx))

        if env:
            env['pywb.cdx'] = cdx

        return result

    def fetch_async(self, url, headers):
        resp = self.live_request(method='GET',
                                 url=url,
                                 headers=headers,
                                 proxies=self.proxies,
                                 verify=False,
                                 stream=True)

        # don't actually read whole response,
        # proxy response for writing it
        resp.close()

    def add_metadata(self, url, headers, data):
        return self.live_request(method='PUTMETA',
                                 url=url,
                                 data=data,
                                 headers=headers,
                                 proxies=self.proxies,
                                 verify=False)

    def get_rewritten(self, *args, **kwargs):
        result = self.fetch_request(*args, **kwargs)

        status_headers, gen, is_rewritten = result

        buff = b''.join(gen)

        return (status_headers, buff)

    def get_video_info(self, url):
        return youtubedl.extract_info(url)


# =================================================================
class YoutubeDLWrapper(object):  # pragma: no cover
    """ YoutubeDL wrapper, inits youtubee-dl if it is available
    """

    def __init__(self):
        try:
            from youtube_dl import YoutubeDL as YoutubeDL
        except ImportError:
            self.ydl = None
            return

        self.ydl = YoutubeDL(dict(simulate=True,
                                  youtube_include_dash_manifest=False))
        self.ydl.add_default_info_extractors()

    def extract_info(self, url):
        if not self.ydl:
            return None

        info = self.ydl.extract_info(url)
        return info


# =================================================================
youtubedl = YoutubeDLWrapper()


# end pywb.rewrite.rewrite_live

# begin pywb.framework.basehandlers
# =================================================================
class BaseHandler(object):
    """
    Represents a base handler class that handles any request
    """

    def __call__(self, wbrequest):  # pragma: no cover
        raise NotImplementedError('Need to implement in derived class')

    def get_wburl_type(self):
        return None


# =================================================================
class WbUrlHandler(BaseHandler):
    """
    Represents a handler which assumes the request contains a WbUrl
    Ensure that the WbUrl is parsed in the request
    """

    def get_wburl_type(self):
        return WbUrl


# end pywb.framework.basehandlers

# begin pywb.framework.cache
# =================================================================
class UwsgiCache(object):  # pragma: no cover
    def __setitem__(self, item, value):
        uwsgi.cache_update(item, value)

    def __getitem__(self, item):
        return uwsgi.cache_get(item)

    def __contains__(self, item):
        return uwsgi.cache_exists(item)

    def __delitem__(self, item):
        uwsgi.cache_del(item)


# =================================================================
class DefaultCache(dict):
    def __getitem__(self, item):
        return self.get(item)


# =================================================================
class RedisCache(object):
    def __init__(self, redis_url):
        # must be of the form redis://host:port/db/key
        redis_url, key = redis_url.rsplit('/', 1)
        self.redis = StrictRedis.from_url(redis_url)
        self.key = key

    def __setitem__(self, item, value):
        self.redis.hset(self.key, item, value)

    def __getitem__(self, item):
        return to_native_str(self.redis.hget(self.key, item), 'utf-8')

    def __contains__(self, item):
        return self.redis.hexists(self.key, item)

    def __delitem__(self, item):
        self.redis.hdel(self.key, item)


# =================================================================
def create_cache(redis_url_key=None):
    if redis_url_key:
        return RedisCache(redis_url_key)

    if uwsgi_cache:  # pragma: no cover
        return UwsgiCache()
    else:
        return DefaultCache()


# end pywb.framework.cache

# begin pywb.framework.archivalrouter

# =================================================================
# ArchivalRouter -- route WB requests in archival mode
# =================================================================
class ArchivalRouter(object):
    def __init__(self, routes, **kwargs):
        self.routes = routes

        # optional port setting may be ignored by wsgi container
        self.port = kwargs.get('port')

        self.fallback = ReferRedirect()

        self.abs_path = kwargs.get('abs_path')

        self.home_view = kwargs.get('home_view')
        self.error_view = kwargs.get('error_view')
        self.info_view = kwargs.get('info_view')

        config = kwargs.get('config', {})
        self.urlrewriter_class = config.get('urlrewriter_class', UrlRewriter)

        self.enable_coll_info = config.get('enable_coll_info', False)

    def __call__(self, env):
        request_uri = self.ensure_rel_uri_set(env)

        for route in self.routes:
            matcher, coll = route.is_handling(request_uri)
            if matcher:
                wbrequest = self.parse_request(route, env, matcher,
                                               coll, request_uri,
                                               use_abs_prefix=self.abs_path)

                return route.handler(wbrequest)

        # Default Home Page
        if request_uri in ['/', '/index.html', '/index.htm']:
            return self.render_home_page(env)

        if self.enable_coll_info and request_uri in ['/collinfo.json']:
            params = env.get('pywb.template_params', {})
            host = WbRequest.make_host_prefix(env)
            return self.info_view.render_response(env=env, host=host, routes=self.routes,
                                                  content_type='application/json',
                                                  **params)

        return self.fallback(env, self) if self.fallback else None

    def parse_request(self, route, env, matcher, coll, request_uri,
                      use_abs_prefix=False):
        matched_str = matcher.group(0)
        rel_prefix = env.get('SCRIPT_NAME', '') + '/'

        if matched_str:
            rel_prefix += matched_str + '/'
            # remove the '/' + rel_prefix part of uri
            wb_url_str = request_uri[len(matched_str) + 2:]
        else:
            # the request_uri is the wb_url, since no coll
            wb_url_str = request_uri[1:]

        wbrequest = route.request_class(env,
                                        request_uri=request_uri,
                                        wb_url_str=wb_url_str,
                                        rel_prefix=rel_prefix,
                                        coll=coll,
                                        use_abs_prefix=use_abs_prefix,
                                        wburl_class=route.handler.get_wburl_type(),
                                        urlrewriter_class=self.urlrewriter_class,
                                        cookie_scope=route.cookie_scope,
                                        rewrite_opts=route.rewrite_opts,
                                        user_metadata=route.user_metadata)

        # Allow for applying of additional filters
        route.apply_filters(wbrequest, matcher)

        return wbrequest

    def render_home_page(self, env):
        if self.home_view:
            params = env.get('pywb.template_params', {})
            return self.home_view.render_response(env=env, routes=self.routes, **params)
        else:
            return None

    # =================================================================
    # adapted from wsgiref.request_uri, but doesn't include domain name
    # and allows all characters which are allowed in the path segment
    # according to: http://tools.ietf.org/html/rfc3986#section-3.3
    # explained here:
    # http://stackoverflow.com/questions/4669692/
    #   valid-characters-for-directory-part-of-a-url-for-short-links

    @staticmethod
    def ensure_rel_uri_set(env):
        """ Return the full requested path, including the query string
        """
        if 'REL_REQUEST_URI' in env:
            return env['REL_REQUEST_URI']

        if not env.get('SCRIPT_NAME') and env.get('REQUEST_URI'):
            env['REL_REQUEST_URI'] = env['REQUEST_URI']
            return env['REL_REQUEST_URI']

        url = quote(env.get('PATH_INFO', ''), safe='/~!$&\'()*+,;=:@')
        query = env.get('QUERY_STRING')
        if query:
            url += '?' + query

        env['REL_REQUEST_URI'] = url
        return url


# =================================================================
# Route by matching regex (or fixed prefix)
# of request uri (excluding first '/')
# =================================================================
class Route(object):
    # match upto next / or ? or end
    SLASH_QUERY_LOOKAHEAD = '(?=/|$|\?)'

    def __init__(self, regex, handler, config=None,
                 request_class=WbRequest,
                 lookahead=SLASH_QUERY_LOOKAHEAD):

        config = config or {}
        self.path = regex
        if regex:
            self.regex = re.compile(regex + lookahead)
        else:
            self.regex = re.compile('')

        self.handler = handler
        self.request_class = request_class

        # collection id from regex group (default 0)
        self.coll_group = int(config.get('coll_group', 0))
        self.cookie_scope = config.get('cookie_scope')
        self.rewrite_opts = config.get('rewrite_opts', {})
        self.user_metadata = config.get('metadata', {})
        self._custom_init(config)

    def is_handling(self, request_uri):
        matcher = self.regex.match(request_uri[1:])
        if not matcher:
            return None, None

        coll = matcher.group(self.coll_group)
        return matcher, coll

    def apply_filters(self, wbrequest, matcher):
        for filter in self.filters:
            last_grp = len(matcher.groups())
            filter_str = filter.format(matcher.group(last_grp))
            wbrequest.query_filter.append(filter_str)

    def _custom_init(self, config):
        self.filters = config.get('filters', [])


# =================================================================
# ReferRedirect -- redirect urls that have 'fallen through'
# based on the referrer settings
# =================================================================
class ReferRedirect:
    def __call__(self, env, the_router):
        referrer = env.get('HTTP_REFERER')

        routes = the_router.routes

        # ensure there is a referrer
        if referrer is None:
            return None

        # get referrer path name
        ref_split = urlsplit(referrer)

        # require that referrer starts with current Host, if any
        curr_host = env.get('HTTP_HOST')
        if curr_host and curr_host != ref_split.netloc:
            return None

        path = ref_split.path

        app_path = env.get('SCRIPT_NAME', '')

        if app_path:
            # must start with current app name, if not root
            if not path.startswith(app_path):
                return None

            path = path[len(app_path):]

        ref_route = None
        ref_request = None

        for route in routes:
            matcher, coll = route.is_handling(path)
            if matcher:
                ref_request = the_router.parse_request(route, env,
                                                       matcher, coll, path)
                ref_route = route
                break

        # must have matched one of the routes with a urlrewriter
        if not ref_request or not ref_request.urlrewriter:
            return None

        rewriter = ref_request.urlrewriter

        rel_request_uri = env['REL_REQUEST_URI']

        timestamp_path = '/' + rewriter.wburl.timestamp + '/'

        # check if timestamp is already part of the path
        if rel_request_uri.startswith(timestamp_path):
            # remove timestamp but leave / to make host relative url
            # 2013/path.html -> /path.html
            rel_request_uri = rel_request_uri[len(timestamp_path) - 1:]

        rewritten_url = rewriter.rewrite(rel_request_uri)

        # if post, can't redirect as that would lost the post data
        # (can't use 307 because FF will show confirmation warning)
        if ref_request.method == 'POST':
            new_wb_url = WbUrl(rewritten_url[len(rewriter.prefix):])
            ref_request.wb_url.url = new_wb_url.url
            return ref_route.handler(ref_request)

        final_url = urlunsplit((ref_split.scheme,
                                ref_split.netloc,
                                rewritten_url,
                                '',
                                ''))

        return WbResponse.redir_response(final_url, status='302 Temp Redirect')


# end pywb.framework.archivalrouter


# begin pywb.framework.proxy_resolvers
# =================================================================
class BaseCollResolver(object):
    def __init__(self, routes, config):
        self.routes = routes
        self.use_default_coll = config.get('use_default_coll')

    @property
    def pre_connect(self):
        return False

    def resolve(self, env):
        route = None
        coll = None
        matcher = None
        ts = None

        proxy_coll, ts = self.get_proxy_coll_ts(env)

        # invalid parsing
        if proxy_coll == '':
            return None, None, None, None, self.select_coll_response(env, proxy_coll)

        if proxy_coll is None and isinstance(self.use_default_coll, str):
            proxy_coll = self.use_default_coll

        if proxy_coll:
            path = '/' + proxy_coll + '/'

            for r in self.routes:
                matcher, c = r.is_handling(path)
                if matcher:
                    route = r
                    coll = c
                    break

            # if no match, return coll selection response
            if not route:
                return None, None, None, None, self.select_coll_response(env, proxy_coll)

        # if 'use_default_coll', find first WbUrl-handling collection
        elif self.use_default_coll:
            raise Exception('use_default_coll: true no longer supported, please specify collection name')
            # for route in self.routes:
            #    if isinstance(route.handler, WbUrlHandler):
            #        return route, route.path, matcher, ts, None

        # otherwise, return the appropriate coll selection response
        else:
            return None, None, None, None, self.select_coll_response(env, proxy_coll)

        return route, coll, matcher, ts, None


# =================================================================
class ProxyAuthResolver(BaseCollResolver):
    DEFAULT_MSG = 'Please enter name of a collection to use with proxy mode'

    def __init__(self, routes, config):
        super(ProxyAuthResolver, self).__init__(routes, config)
        self.auth_msg = config.get('auth_msg', self.DEFAULT_MSG)

    @property
    def pre_connect(self):
        return True

    @property
    def supports_switching(self):
        return False

    def get_proxy_coll_ts(self, env):
        proxy_auth = env.get('HTTP_PROXY_AUTHORIZATION')

        if not proxy_auth:
            return None, None

        proxy_coll = self.read_basic_auth_coll(proxy_auth)
        return proxy_coll, None

    def select_coll_response(self, env, default_coll=None):
        proxy_msg = 'Basic realm="{0}"'.format(self.auth_msg)

        headers = [('Content-Type', 'text/plain'),
                   ('Proxy-Authenticate', proxy_msg)]

        status_headers = StatusAndHeaders('407 Proxy Authentication', headers)

        value = self.auth_msg

        return WbResponse(status_headers, value=[value.encode('utf-8')])

    @staticmethod
    def read_basic_auth_coll(value):
        parts = value.split(' ')
        if parts[0].lower() != 'basic':
            return ''

        if len(parts) != 2:
            return ''

        user_pass = base64.b64decode(parts[1].encode('utf-8'))
        return to_native_str(user_pass.split(b':')[0])


# =================================================================
class IPCacheResolver(BaseCollResolver):
    def __init__(self, routes, config):
        super(IPCacheResolver, self).__init__(routes, config)
        self.cache = create_cache(config.get('redis_cache_key'))
        self.magic_name = config['magic_name']

    @property
    def supports_switching(self):
        return False

    def _get_ip(self, env):
        ip = env['REMOTE_ADDR']
        qs = env.get('pywb.proxy_query')
        if qs:
            res = parse_qs(qs)

            if 'ip' in res:
                ip = res['ip'][0]

        return ip

    def select_coll_response(self, env, default_coll=None):
        raise WbException('Invalid Proxy Collection Specified: ' + str(default_coll))

    def get_proxy_coll_ts(self, env):
        ip = env['REMOTE_ADDR']
        qs = env.get('pywb.proxy_query')

        if qs:
            res = parse_qs(qs)

            if 'ip' in res:
                ip = res['ip'][0]

            if 'delete' in res:
                del self.cache[ip + ':c']
                del self.cache[ip + ':t']
            else:
                if 'coll' in res:
                    self.cache[ip + ':c'] = res['coll'][0]

                if 'ts' in res:
                    self.cache[ip + ':t'] = res['ts'][0]

        coll = self.cache[ip + ':c']
        ts = self.cache[ip + ':t']
        return coll, ts

    def resolve(self, env):
        server_name = env['pywb.proxy_host']

        if self.magic_name in server_name:
            response = self.handle_magic_page(env)
            if response:
                return None, None, None, None, response

        return super(IPCacheResolver, self).resolve(env)

    def handle_magic_page(self, env):
        coll, ts = self.get_proxy_coll_ts(env)
        ip = self._get_ip(env)
        res = json.dumps({'ip': ip, 'coll': coll, 'ts': ts})
        return WbResponse.text_response(res, content_type='application/json')


# =================================================================
class CookieResolver(BaseCollResolver):
    SESH_COOKIE_NAME = '__pywb_proxy_sesh'

    def __init__(self, routes, config):
        super(CookieResolver, self).__init__(routes, config)
        self.magic_name = config['magic_name']
        self.sethost_prefix = '-sethost.' + self.magic_name + '.'
        self.set_prefix = '-set.' + self.magic_name

        self.cookie_name = config.get('cookie_name', self.SESH_COOKIE_NAME)
        self.proxy_select_view = config.get('proxy_select_view')

        self.extra_headers = config.get('extra_headers')

        self.cache = create_cache()

    @property
    def supports_switching(self):
        return True

    def get_proxy_coll_ts(self, env):
        coll, ts, sesh_id = self.get_coll(env)
        return coll, ts

    def select_coll_response(self, env, default_coll=None):
        return self.make_magic_response('auto',
                                        env['REL_REQUEST_URI'],
                                        env)

    def resolve(self, env):
        server_name = env['pywb.proxy_host']

        if ('.' + self.magic_name) in server_name:
            response = self.handle_magic_page(env)
            if response:
                return None, None, None, None, response

        return super(CookieResolver, self).resolve(env)

    def handle_magic_page(self, env):
        request_url = env['REL_REQUEST_URI']
        parts = urlsplit(request_url)
        server_name = env['pywb.proxy_host']

        path_url = parts.path[1:]
        if parts.query:
            path_url += '?' + parts.query

        if server_name.startswith('auto'):
            coll, ts, sesh_id = self.get_coll(env)

            if coll:
                return self.make_sethost_cookie_response(sesh_id,
                                                         path_url,
                                                         env)
            else:
                return self.make_magic_response('select', path_url, env)

        elif server_name.startswith('query.'):
            wb_url = WbUrl(path_url)

            # only dealing with specific timestamp setting
            if wb_url.is_query():
                return None

            coll, ts, sesh_id = self.get_coll(env)
            if not coll:
                return self.make_magic_response('select', path_url, env)

            self.set_ts(sesh_id, wb_url.timestamp)
            return self.make_redir_response(wb_url.url)

        elif server_name.endswith(self.set_prefix):
            old_sesh_id = extract_client_cookie(env, self.cookie_name)
            sesh_id = self.create_renew_sesh_id(old_sesh_id)

            if sesh_id != old_sesh_id:
                headers = self.make_cookie_headers(sesh_id, self.magic_name)
            else:
                headers = None

            coll = server_name[:-len(self.set_prefix)]

            # set sesh value
            self.set_coll(sesh_id, coll)

            return self.make_sethost_cookie_response(sesh_id, path_url, env,
                                                     headers=headers)

        elif self.sethost_prefix in server_name:
            inx = server_name.find(self.sethost_prefix)
            sesh_id = server_name[:inx]

            domain = server_name[inx + len(self.sethost_prefix):]

            headers = self.make_cookie_headers(sesh_id, domain)

            full_url = env['pywb.proxy_scheme'] + '://' + domain
            full_url += '/' + path_url
            return self.make_redir_response(full_url, headers=headers)

        elif 'select.' in server_name:
            coll, ts, sesh_id = self.get_coll(env)

            route_temp = '-set.' + self.magic_name + '/' + path_url

            return (self.proxy_select_view.
                    render_response(routes=self.routes,
                                    route_temp=route_temp,
                                    coll=coll,
                                    url=path_url))
            # else:
            #    msg = 'Invalid Magic Path: ' + url
            #    print msg
            #    return WbResponse.text_response(msg, status='404 Not Found')

    def make_cookie_headers(self, sesh_id, domain):
        cookie_val = '{0}={1}; Path=/; Domain=.{2}; HttpOnly'
        cookie_val = cookie_val.format(self.cookie_name, sesh_id, domain)
        headers = [('Set-Cookie', cookie_val)]
        return headers

    def make_sethost_cookie_response(self, sesh_id, path_url,
                                     env, headers=None):
        if '://' not in path_url:
            path_url = 'http://' + path_url

        path_parts = urlsplit(path_url)

        new_url = path_parts.path[1:]
        if path_parts.query:
            new_url += '?' + path_parts.query

        return self.make_magic_response(sesh_id + '-sethost', new_url, env,
                                        suffix=path_parts.netloc,
                                        headers=headers)

    def make_magic_response(self, prefix, url, env,
                            suffix=None, headers=None):
        full_url = env['pywb.proxy_scheme'] + '://' + prefix + '.'
        full_url += self.magic_name
        if suffix:
            full_url += '.' + suffix
        full_url += '/' + url
        return self.make_redir_response(full_url, headers=headers)

    def set_coll(self, sesh_id, coll):
        self.cache[sesh_id + ':c'] = coll

    def set_ts(self, sesh_id, ts):
        if ts:
            self.cache[sesh_id + ':t'] = ts
        # this ensures that omitting timestamp will reset to latest
        # capture by deleting the cache entry
        else:
            del self.cache[sesh_id + ':t']

    def get_coll(self, env):
        sesh_id = extract_client_cookie(env, self.cookie_name)

        coll = None
        ts = None
        if sesh_id:
            coll = self.cache[sesh_id + ':c']
            ts = self.cache[sesh_id + ':t']

        return coll, ts, sesh_id

    def create_renew_sesh_id(self, sesh_id, force=False):
        # if sesh_id in self.cache and not force:
        if sesh_id and ((sesh_id + ':c') in self.cache) and not force:
            return sesh_id

        sesh_id = base64.b32encode(os.urandom(5)).lower()
        return to_native_str(sesh_id)

    def make_redir_response(self, url, headers=None):
        if not headers:
            headers = []

        if self.extra_headers:
            for name, value in six.iteritems(self.extra_headers):
                headers.append((name, value))

        return WbResponse.redir_response(url, headers=headers)


# end pywb.framework.proxy_resolvers

# begin pywb.framework.proxy
# =================================================================
class ProxyArchivalRouter(ArchivalRouter):
    """
    A router which combines both archival and proxy modes support
    First, request is treated as a proxy request using ProxyRouter
    Second, if not handled by the router, it is treated as a regular
    archival mode request.
    """

    def __init__(self, routes, **kwargs):
        super(ProxyArchivalRouter, self).__init__(routes, **kwargs)
        self.proxy = ProxyRouter(routes, **kwargs)

    def __call__(self, env):
        response = self.proxy(env)
        if response:
            return response

        response = super(ProxyArchivalRouter, self).__call__(env)
        if response:
            return response


# =================================================================
class ProxyRouter(object):
    """
    A router which supports http proxy mode requests
    Handles requests of the form: GET http://example.com

    The router returns latest capture by default.
    However, if Memento protocol support is enabled,
    the memento Accept-Datetime header can be used
    to select specific capture.
    See: http://www.mementoweb.org/guide/rfc/#Pattern1.3
    for more details.
    """

    BLOCK_SIZE = 4096
    DEF_MAGIC_NAME = 'pywb.proxy'
    BUFF_RESPONSE_MEM_SIZE = 1024 * 1024

    CERT_DL_PEM = '/pywb-ca.pem'
    CERT_DL_P12 = '/pywb-ca.p12'

    CA_ROOT_FILE = './ca/pywb-ca.pem'
    CA_ROOT_NAME = 'pywb https proxy replay CA'
    CA_CERTS_DIR = './ca/certs/'

    EXTRA_HEADERS = {'cache-control': 'no-cache',
                     'connection': 'close',
                     'p3p': 'CP="NOI ADM DEV COM NAV OUR STP"'}

    def __init__(self, routes, **kwargs):
        self.error_view = kwargs.get('error_view')

        proxy_options = kwargs.get('config', {})
        if proxy_options:
            proxy_options = proxy_options.get('proxy_options', {})

        self.magic_name = proxy_options.get('magic_name')
        if not self.magic_name:
            self.magic_name = self.DEF_MAGIC_NAME
            proxy_options['magic_name'] = self.magic_name

        self.extra_headers = proxy_options.get('extra_headers')
        if not self.extra_headers:
            self.extra_headers = self.EXTRA_HEADERS
            proxy_options['extra_headers'] = self.extra_headers

        res_type = proxy_options.get('cookie_resolver', True)
        if res_type == 'auth' or not res_type:
            self.resolver = ProxyAuthResolver(routes, proxy_options)
        elif res_type == 'ip':
            self.resolver = IPCacheResolver(routes, proxy_options)
        # elif res_type == True or res_type == 'cookie':
        #    self.resolver = CookieResolver(routes, proxy_options)
        else:
            self.resolver = CookieResolver(routes, proxy_options)

        self.use_banner = proxy_options.get('use_banner', True)
        self.use_wombat = proxy_options.get('use_client_rewrite', True)

        self.proxy_cert_dl_view = proxy_options.get('proxy_cert_download_view')

        if not proxy_options.get('enable_https_proxy'):
            self.ca = None
            return

        try:
            from certauth.certauth import CertificateAuthority
        except ImportError:  # pragma: no cover
            print('HTTPS proxy is not available as the "certauth" module ' +
                  'is not installed')
            print('Please install via "pip install certauth" ' +
                  'to enable HTTPS support')
            self.ca = None
            return

        # HTTPS Only Options
        ca_file = proxy_options.get('root_ca_file', self.CA_ROOT_FILE)

        # attempt to create the root_ca_file if doesn't exist
        # (generally recommended to create this seperately)
        ca_name = proxy_options.get('root_ca_name', self.CA_ROOT_NAME)

        certs_dir = proxy_options.get('certs_dir', self.CA_CERTS_DIR)
        self.ca = CertificateAuthority(ca_file=ca_file,
                                       certs_dir=certs_dir,
                                       ca_name=ca_name)

        self.use_wildcard = proxy_options.get('use_wildcard_certs', True)

    def __call__(self, env):
        is_https = (env['REQUEST_METHOD'] == 'CONNECT')
        ArchivalRouter.ensure_rel_uri_set(env)

        # for non-https requests, check non-proxy urls
        if not is_https:
            url = env['REL_REQUEST_URI']

            if not url.startswith(('http://', 'https://')):
                return None

            env['pywb.proxy_scheme'] = 'http'

        route = None
        coll = None
        matcher = None
        response = None
        ts = None

        # check resolver, for pre connect resolve
        if self.resolver.pre_connect:
            route, coll, matcher, ts, response = self.resolver.resolve(env)
            if response:
                return response

        # do connect, then get updated url
        if is_https:
            response = self.handle_connect(env)
            if response:
                return response

            url = env['REL_REQUEST_URI']
        else:
            parts = urlsplit(env['REL_REQUEST_URI'])
            hostport = parts.netloc.split(':', 1)
            env['pywb.proxy_host'] = hostport[0]
            env['pywb.proxy_port'] = hostport[1] if len(hostport) == 2 else ''
            env['pywb.proxy_req_uri'] = parts.path
            if parts.query:
                env['pywb.proxy_req_uri'] += '?' + parts.query
                env['pywb.proxy_query'] = parts.query

        if self.resolver.supports_switching:
            env['pywb_proxy_magic'] = self.magic_name

        # route (static) and other resources to archival replay
        if env['pywb.proxy_host'] == self.magic_name:
            env['REL_REQUEST_URI'] = env['pywb.proxy_req_uri']

            # special case for proxy install
            response = self.handle_cert_install(env)
            if response:
                return response

            return None

        # check resolver, post connect
        if not self.resolver.pre_connect:
            route, coll, matcher, ts, response = self.resolver.resolve(env)
            if response:
                return response

        rel_prefix = ''

        custom_prefix = env.get('HTTP_PYWB_REWRITE_PREFIX', '')
        if custom_prefix:
            host_prefix = custom_prefix
            urlrewriter_class = UrlRewriter
            abs_prefix = True
            # always rewrite to absolute here
            rewrite_opts = dict(no_match_rel=True)
        else:
            host_prefix = env['pywb.proxy_scheme'] + '://' + self.magic_name
            urlrewriter_class = SchemeOnlyUrlRewriter
            abs_prefix = False
            rewrite_opts = {}

        # special case for proxy calendar
        if (env['pywb.proxy_host'] == 'query.' + self.magic_name):
            url = env['pywb.proxy_req_uri'][1:]
            rel_prefix = '/'

        if ts is not None:
            url = ts + '/' + url

        wbrequest = route.request_class(env,
                                        request_uri=url,
                                        wb_url_str=url,
                                        coll=coll,
                                        host_prefix=host_prefix,
                                        rel_prefix=rel_prefix,
                                        wburl_class=route.handler.get_wburl_type(),
                                        urlrewriter_class=urlrewriter_class,
                                        use_abs_prefix=abs_prefix,
                                        rewrite_opts=rewrite_opts,
                                        is_proxy=True)

        if matcher:
            route.apply_filters(wbrequest, matcher)

        # full rewrite and banner
        if self.use_wombat and self.use_banner:
            wbrequest.wb_url.mod = ''
        elif self.use_banner:
            # banner only, no rewrite
            wbrequest.wb_url.mod = 'bn_'
        else:
            # unaltered, no rewrite or banner
            wbrequest.wb_url.mod = 'uo_'

        response = route.handler(wbrequest)
        if not response:
            return None

        # add extra headers for replay responses
        if wbrequest.wb_url and wbrequest.wb_url.is_replay():
            response.status_headers.replace_headers(self.extra_headers)

        # check for content-length
        res = response.status_headers.get_header('content-length')
        try:
            if int(res) > 0:
                return response
        except:
            pass

        # need to either chunk or buffer to get content-length
        if env.get('SERVER_PROTOCOL') == 'HTTP/1.1':
            response.status_headers.remove_header('content-length')
            response.status_headers.headers.append(('Transfer-Encoding', 'chunked'))
            response.body = self._chunk_encode(response.body)
        else:
            response.body = self._buffer_response(response.status_headers,
                                                  response.body)

        return response

    @staticmethod
    def _chunk_encode(orig_iter):
        for chunk in orig_iter:
            if not len(chunk):
                continue
            chunk_len = b'%X\r\n' % len(chunk)
            yield chunk_len
            yield chunk
            yield b'\r\n'

        yield b'0\r\n\r\n'

    @staticmethod
    def _buffer_response(status_headers, iterator):
        out = SpooledTemporaryFile(ProxyRouter.BUFF_RESPONSE_MEM_SIZE)
        size = 0

        for buff in iterator:
            size += len(buff)
            out.write(buff)

        content_length_str = str(size)
        # remove existing content length
        status_headers.replace_header('Content-Length',
                                      content_length_str)

        out.seek(0)
        return RewriteContent.stream_to_gen(out)

    def get_request_socket(self, env):
        if not self.ca:
            return None

        sock = None

        if env.get('uwsgi.version'):  # pragma: no cover
            try:
                import uwsgi
                fd = uwsgi.connection_fd()
                conn = socket.fromfd(fd, socket.AF_INET, socket.SOCK_STREAM)
                try:
                    sock = socket.socket(_sock=conn)
                except:
                    sock = conn
            except Exception as e:
                pass
        elif env.get('gunicorn.socket'):  # pragma: no cover
            sock = env['gunicorn.socket']

        if not sock:
            # attempt to find socket from wsgi.input
            input_ = env.get('wsgi.input')
            if input_:
                if hasattr(input_, '_sock'):  # pragma: no cover
                    raw = input_._sock
                    sock = socket.socket(_sock=raw)  # pragma: no cover
                elif hasattr(input_, 'raw'):
                    sock = input_.raw._sock

        return sock

    def handle_connect(self, env):
        sock = self.get_request_socket(env)
        if not sock:
            return WbResponse.text_response('HTTPS Proxy Not Supported',
                                            '405 HTTPS Proxy Not Supported')

        sock.send(b'HTTP/1.0 200 Connection Established\r\n')
        sock.send(b'Proxy-Connection: close\r\n')
        sock.send(b'Server: pywb proxy\r\n')
        sock.send(b'\r\n')

        hostname, port = env['REL_REQUEST_URI'].split(':')

        if not self.use_wildcard:
            certfile = self.ca.cert_for_host(hostname)
        else:
            certfile = self.ca.get_wildcard_cert(hostname)

        try:
            ssl_sock = ssl.wrap_socket(sock,
                                       server_side=True,
                                       certfile=certfile,
                                       # ciphers="ALL",
                                       suppress_ragged_eofs=False,
                                       ssl_version=ssl.PROTOCOL_SSLv23
                                       )
            env['pywb.proxy_ssl_sock'] = ssl_sock

            buffreader = BufferedReader(ssl_sock, block_size=self.BLOCK_SIZE)

            statusline = to_native_str(buffreader.readline().rstrip())

        except Exception as se:
            raise BadRequestException(se.message)

        statusparts = statusline.split(' ')

        if len(statusparts) < 3:
            raise BadRequestException('Invalid Proxy Request: ' + statusline)

        env['REQUEST_METHOD'] = statusparts[0]
        env['REL_REQUEST_URI'] = ('https://' +
                                  env['REL_REQUEST_URI'].replace(':443', '') +
                                  statusparts[1])

        env['SERVER_PROTOCOL'] = statusparts[2].strip()

        env['pywb.proxy_scheme'] = 'https'

        env['pywb.proxy_host'] = hostname
        env['pywb.proxy_port'] = port
        env['pywb.proxy_req_uri'] = statusparts[1]

        queryparts = env['REL_REQUEST_URI'].split('?', 1)
        env['PATH_INFO'] = queryparts[0]
        env['QUERY_STRING'] = queryparts[1] if len(queryparts) > 1 else ''
        env['pywb.proxy_query'] = env['QUERY_STRING']

        while True:
            line = to_native_str(buffreader.readline())
            if line:
                line = line.rstrip()

            if not line:
                break

            parts = line.split(':', 1)
            if len(parts) < 2:
                continue

            name = parts[0].strip()
            value = parts[1].strip()

            name = name.replace('-', '_').upper()

            if name not in ('CONTENT_LENGTH', 'CONTENT_TYPE'):
                name = 'HTTP_' + name

            env[name] = value

        env['wsgi.input'] = buffreader
        # remain = buffreader.rem_length()
        # if remain > 0:
        # remainder = buffreader.read()
        # env['wsgi.input'] = BufferedReader(BytesIO(remainder))
        # remainder = buffreader.read(self.BLOCK_SIZE)
        # env['wsgi.input'] = BufferedReader(ssl_sock,
        #                                   block_size=self.BLOCK_SIZE,
        #                                   starting_data=remainder)

    def handle_cert_install(self, env):
        if env['pywb.proxy_req_uri'] in ('/', '/index.html', '/index.html'):
            available = (self.ca is not None)

            if self.proxy_cert_dl_view:
                return (self.proxy_cert_dl_view.
                        render_response(available=available,
                                        pem_path=self.CERT_DL_PEM,
                                        p12_path=self.CERT_DL_P12))

        elif env['pywb.proxy_req_uri'] == self.CERT_DL_PEM:
            if not self.ca:
                return None

            buff = b''
            with open(self.ca.ca_file, 'rb') as fh:
                buff = fh.read()

            content_type = 'application/x-x509-ca-cert'
            headers = [('Content-Length', str(len(buff)))]

            return WbResponse.bin_stream([buff],
                                         content_type=content_type,
                                         headers=headers)

        elif env['pywb.proxy_req_uri'] == self.CERT_DL_P12:
            if not self.ca:
                return None

            buff = self.ca.get_root_PKCS12()

            content_type = 'application/x-pkcs12'
            headers = [('Content-Length', str(len(buff)))]

            return WbResponse.bin_stream([buff],
                                         content_type=content_type,
                                         headers=headers)


# end  pywb.framework.proxy


# begin pywb.framework.memento
# =================================================================
class MementoReqMixin(object):
    def _parse_extra(self):
        if not self.wb_url:
            return

        if self.wb_url.type != self.wb_url.LATEST_REPLAY:
            return

        self.options['is_timegate'] = True

        accept_datetime = self.env.get('HTTP_ACCEPT_DATETIME')
        if not accept_datetime:
            return

        try:
            timestamp = http_date_to_timestamp(accept_datetime)
        except Exception:
            raise BadRequestException('Invalid Accept-Datetime: ' +
                                      accept_datetime)

        # note: this changes from LATEST_REPLAY -> REPLAY
        self.wb_url.set_replay_timestamp(timestamp)


# =================================================================
class MementoRequest(MementoReqMixin, WbRequest):
    pass


# =================================================================
class MementoRespMixin(object):
    def _init_derived(self, params):
        wbrequest = params.get('wbrequest')
        is_redirect = params.get('memento_is_redir', False)
        cdx = params.get('cdx')

        if not wbrequest or not wbrequest.wb_url:
            return

        mod = wbrequest.options.get('replay_mod', '')

        # is_top_frame = wbrequest.wb_url.is_top_frame
        is_top_frame = wbrequest.options.get('is_top_frame', False)

        is_timegate = (wbrequest.options.get('is_timegate', False) and
                       not is_top_frame)

        if is_timegate:
            self.status_headers.headers.append(('Vary', 'accept-datetime'))

        # Determine if memento:
        is_memento = False
        is_original = False

        # if no cdx included, not a memento, unless top-frame special
        if not cdx:
            # special case: include the headers but except Memento-Datetime
            # since this is really an intermediate resource
            if is_top_frame:
                is_memento = True

        # otherwise, if in proxy mode, then always a memento
        elif wbrequest.options['is_proxy']:
            is_memento = True
            is_original = True

        # otherwise only if timestamp replay (and not a timegate)
        # elif not is_timegate:
        #    is_memento = (wbrequest.wb_url.type == wbrequest.wb_url.REPLAY)
        elif not is_redirect:
            is_memento = (wbrequest.wb_url.is_replay())

        link = []
        req_url = wbrequest.wb_url.url

        if is_memento or is_timegate:
            url = req_url
            if cdx:
                ts = cdx['timestamp']
                url = cdx['url']
            # for top frame
            elif wbrequest.wb_url.timestamp:
                ts = wbrequest.wb_url.timestamp
            else:
                ts = None

            if ts:
                http_date = timestamp_to_http_date(ts)

                if is_memento:
                    self.status_headers.headers.append(('Memento-Datetime',
                                                        http_date))

                canon_link = wbrequest.urlrewriter.get_new_url(mod=mod,
                                                               timestamp=ts,
                                                               url=url)

                # set in replay_views -- Must set content location
                # if is_memento and is_timegate:
                #    self.status_headers.headers.append(('Content-Location',
                #                                        canon_link))

                # don't set memento link for very long urls...
                if len(canon_link) < 512:
                    link.append(self.make_memento_link(canon_link,
                                                       'memento',
                                                       http_date))

        if is_original and is_timegate:
            link.append(self.make_link(req_url, 'original timegate'))
        else:
            link.append(self.make_link(req_url, 'original'))

        # for now, include timemap only in non-proxy mode
        if not wbrequest.options['is_proxy'] and (is_memento or is_timegate):
            link.append(self.make_timemap_link(wbrequest))

        if is_memento and not is_timegate:
            timegate = wbrequest.urlrewriter.get_new_url(mod=mod, timestamp='')
            link.append(self.make_link(timegate, 'timegate'))

        link = ', '.join(link)

        self.status_headers.headers.append(('Link', link))

    def make_link(self, url, type):
        return '<{0}>; rel="{1}"'.format(url, type)

    def make_memento_link(self, url, type_, dt):
        return '<{0}>; rel="{1}"; datetime="{2}"'.format(url, type_, dt)

    def make_timemap_link(self, wbrequest):
        format_ = '<{0}>; rel="timemap"; type="{1}"'

        url = wbrequest.urlrewriter.get_new_url(mod='timemap',
                                                timestamp='',
                                                type=wbrequest.wb_url.QUERY)

        return format_.format(url, LINK_FORMAT)


# =================================================================
class MementoResponse(MementoRespMixin, WbResponse):
    pass


# =================================================================
def make_timemap_memento_link(cdx, prefix, datetime=None,
                              rel='memento', end=',\n', mod=''):
    memento = '<{0}>; rel="{1}"; datetime="{2}"' + end

    string = WbUrl.to_wburl_str(url=cdx['url'],
                                mod=mod,
                                timestamp=cdx['timestamp'],
                                type=WbUrl.REPLAY)

    url = prefix + string

    if not datetime:
        datetime = timestamp_to_http_date(cdx['timestamp'])

    return memento.format(url, rel, datetime)


# =================================================================
def make_timemap(wbrequest, cdx_lines):
    prefix = wbrequest.wb_prefix
    url = wbrequest.wb_url.url
    mod = wbrequest.options.get('replay_mod', '')

    # get first memento as it'll be used for 'from' field
    try:
        first_cdx = six.next(cdx_lines)
        from_date = timestamp_to_http_date(first_cdx['timestamp'])
    except StopIteration:
        first_cdx = None

    if first_cdx:
        # timemap link
        timemap = ('<{0}>; rel="self"; ' +
                   'type="application/link-format"; from="{1}",\n')
        yield timemap.format(prefix + wbrequest.wb_url.to_str(),
                             from_date)

    # original link
    original = '<{0}>; rel="original",\n'
    yield original.format(url)

    # timegate link
    timegate = '<{0}>; rel="timegate",\n'
    timegate_url = WbUrl.to_wburl_str(url=url,
                                      mod=mod,
                                      type=WbUrl.LATEST_REPLAY)

    yield timegate.format(prefix + timegate_url)

    if not first_cdx:
        # terminating timemap link, no from
        timemap = ('<{0}>; rel="self"; type="application/link-format"')
        yield timemap.format(prefix + wbrequest.wb_url.to_str())
        return

    # first memento link
    yield make_timemap_memento_link(first_cdx, prefix,
                                    datetime=from_date, mod=mod)

    prev_cdx = None

    for cdx in cdx_lines:
        if prev_cdx:
            yield make_timemap_memento_link(prev_cdx, prefix, mod=mod)

        prev_cdx = cdx

    # last memento link, if any
    if prev_cdx:
        yield make_timemap_memento_link(prev_cdx, prefix, end='', mod=mod)


# end pywb.framework.memento


# begin pywb.webapp.views
# =================================================================
class template_filter(object):
    """
    Decorator for registering a function as a jinja2 filter
    If optional argument is supplied, it is used as the filter name
    Otherwise, the func name is the filter name
    """

    def __init__(self, param=None):
        self.name = param

    def __call__(self, func):
        name = self.name
        if not name:
            name = func.__name__

        FILTERS[name] = func
        return func


# =================================================================
# Filters
@template_filter()
def format_ts(value, format_='%a, %b %d %Y %H:%M:%S'):
    if format_ == '%s':
        return timestamp_to_sec(value)
    else:
        value = timestamp_to_datetime(value)
        return value.strftime(format_)


@template_filter('urlsplit')
def get_urlsplit(url):
    split = urlsplit(url)
    return split


@template_filter()
def is_wb_handler(obj):
    if not hasattr(obj, 'handler'):
        return False

    return obj.handler.__class__.__name__ == "WBHandler"


@template_filter()
def tojson(obj):
    return json.dumps(obj)


# =================================================================
class FileOnlyPackageLoader(PackageLoader):
    def get_source(self, env, template):
        dir_, file_ = os.path.split(template)
        return super(FileOnlyPackageLoader, self).get_source(env, file_)


# =================================================================
class RelEnvironment(Environment):
    """Override join_path() to enable relative template paths."""

    def join_path(self, template, parent):
        return os.path.join(os.path.dirname(parent), template)


# =================================================================
class J2TemplateView(object):
    shared_jinja_env = None

    def __init__(self, filename):
        self.template_file = filename
        self.jinja_env = self.init_shared_env()

    @staticmethod
    def init_shared_env(paths=['templates', '.', '/'],
                        packages=['pywb'],
                        overlay_env=None):

        if J2TemplateView.shared_jinja_env:
            return J2TemplateView.shared_jinja_env

        loaders = J2TemplateView._add_loaders(paths, packages)
        loader = ChoiceLoader(loaders)

        if overlay_env:
            jinja_env = overlay_env.overlay(loader=loader, trim_blocks=True)
        else:
            jinja_env = RelEnvironment(loader=loader, trim_blocks=True)

        jinja_env.filters.update(FILTERS)
        J2TemplateView.shared_jinja_env = jinja_env
        return jinja_env

    @staticmethod
    def _add_loaders(paths, packages):
        loaders = []
        # add loaders for paths
        for path in paths:
            loaders.append(FileSystemLoader(path))

        # add loaders for all specified packages
        for package in packages:
            loaders.append(FileOnlyPackageLoader(package))

        return loaders

    def render_to_string(self, **kwargs):
        template = self.jinja_env.get_template(self.template_file)

        wbrequest = kwargs.get('wbrequest')
        if wbrequest:
            params = wbrequest.env.get('pywb.template_params')
            if params:
                kwargs.update(params)

        template_result = template.render(**kwargs)

        return template_result

    def render_response(self, **kwargs):
        template_result = self.render_to_string(**kwargs)
        status = kwargs.get('status', '200 OK')
        content_type = kwargs.get('content_type', 'text/html; charset=utf-8')
        return WbResponse.text_response(template_result,
                                        status=status,
                                        content_type=content_type)


# =================================================================
def init_view(config, key, view_class=J2TemplateView):
    filename = config.get(key)
    if not filename:
        return None

    logging.debug('Adding {0}: {1}'.format(key, filename))
    return view_class(filename)


# =================================================================
class HeadInsertView(J2TemplateView):
    def create_insert_func(self, wbrequest,
                           include_ts=True):

        if wbrequest.options['is_ajax']:
            return None

        url = wbrequest.wb_url.get_url()

        top_url = wbrequest.wb_prefix
        top_url += wbrequest.wb_url.to_str(mod=wbrequest.final_mod)

        include_wombat = not wbrequest.wb_url.is_banner_only

        def make_head_insert(rule, cdx):
            cdx['url'] = url
            return (self.render_to_string(wbrequest=wbrequest,
                                          cdx=cdx,
                                          top_url=top_url,
                                          include_ts=include_ts,
                                          include_wombat=include_wombat,
                                          banner_html=self.banner_html,
                                          rule=rule))

        return make_head_insert

    @staticmethod
    def init_from_config(config):
        view = config.get('head_insert_view')
        if not view:
            html = config.get('head_insert_html', 'templates/head_insert.html')

            if html:
                banner_html = config.get('banner_html', 'banner.html')
                view = HeadInsertView(html)
                logging.debug('Adding HeadInsert: {0}, Banner {1}'.
                              format(html, banner_html))

                view.banner_html = banner_html

        return view


# =================================================================
# query views
# =================================================================
class J2HtmlCapturesView(J2TemplateView):
    def render_response(self, wbrequest, cdx_lines, **kwargs):
        def format_cdx_lines():
            for cdx in cdx_lines:
                cdx['_orig_url'] = cdx['url']
                cdx['url'] = wbrequest.wb_url.get_url(url=cdx['url'])
                yield cdx

        return J2TemplateView.render_response(self,
                                              cdx_lines=list(format_cdx_lines()),
                                              url=wbrequest.wb_url.get_url(),
                                              type=wbrequest.wb_url.type,
                                              prefix=wbrequest.wb_prefix,
                                              **kwargs)


# =================================================================
class MementoTimemapView(object):
    def render_response(self, wbrequest, cdx_lines, **kwargs):
        memento_lines = make_timemap(wbrequest, cdx_lines)

        return WbResponse.text_stream(memento_lines,
                                      content_type=LINK_FORMAT)


# end pywb.webapp.views

# begin pywb.webapp.rangecache
# =================================================================
class RangeCache(object):
    def __init__(self):
        self.cache = create_cache()
        self.temp_dir = None
        atexit.register(self.cleanup)

    def cleanup(self):
        if self.temp_dir:  # pragma: no cover
            print('Removing: ' + self.temp_dir)
            rmtree(self.temp_dir, True)
            self.temp_dir = None

    def handle_range(self, wbrequest, key, wbresponse_func,
                     url, start, end, use_206):
        # key must be set
        assert (key)
        if key not in self.cache:
            wbrequest.custom_params['noredir'] = True
            response = wbresponse_func()

            # only cache 200 responses
            if not response.status_headers.get_statuscode().startswith('200'):
                return response.status_headers, response.body

            if not self.temp_dir:
                self.temp_dir = mkdtemp(prefix='_pywbcache')
            else:
                pass
                # self._check_dir_size(self.temp_dir)

            with NamedTemporaryFile(delete=False, dir=self.temp_dir) as fh:
                for obj in response.body:
                    fh.write(obj)

                name = fh.name

            spec = dict(name=fh.name,
                        headers=response.status_headers.headers)

            self.cache[key] = yaml.dump(spec)
        else:
            spec = yaml.load(self.cache[key])

            spec['headers'] = [tuple(x) for x in spec['headers']]

        filelen = os.path.getsize(spec['name'])

        maxlen = filelen - start

        if end:
            maxlen = min(maxlen, end - start + 1)

        def read_range():
            with open(spec['name'], 'rb') as fh:
                fh.seek(start)
                fh = LimitReader.wrap_stream(fh, maxlen)
                while True:
                    buf = fh.read()
                    if not buf:
                        break

                    yield buf

        status_headers = StatusAndHeaders('200 OK', spec['headers'])

        if use_206:
            StatusAndHeaders.add_range(status_headers, start,
                                       maxlen,
                                       filelen)

        status_headers.replace_header('Content-Length', str(maxlen))

        return status_headers, read_range()


# =================================================================
range_cache = RangeCache()


# end pywb.webapp.rangecache


# begin pywb.webapp.replay_views

# =================================================================
class CaptureException(WbException):
    """
    raised to indicate an issue with a specific capture
    and will be caught and result in a retry, if possible
    if not, will result in a 502
    """

    def status(self):
        return '502 Internal Server Error'


# =================================================================
class ReplayView(object):
    STRIP_SCHEME_WWW = re.compile('^([\w]+:[/]*(?:www[\d]*\.)?)?(.*?)$')

    def __init__(self, content_loader, config):
        self.content_loader = content_loader

        framed = config.get('framed_replay')
        self.content_rewriter = RewriteContent(is_framed_replay=framed)

        self.head_insert_view = HeadInsertView.init_from_config(config)

        self.buffer_response = config.get('buffer_response', True)
        self.buffer_max_size = config.get('buffer_max_size', 16384)

        self.redir_to_exact = config.get('redir_to_exact', True)

        memento = config.get('enable_memento', False)
        if memento:
            self.response_class = MementoResponse
        else:
            self.response_class = WbResponse

        self.enable_range_cache = config.get('enable_ranges', True)

        self._reporter = config.get('reporter')

    def render_content(self, wbrequest, cdx_lines, cdx_loader):
        last_e = None
        first = True

        # cdx_lines = args[0]
        # cdx_loader = args[1]

        # List of already failed w/arcs
        failed_files = []

        response = None

        # Iterate over the cdx until find one that works
        # The cdx should already be sorted in
        # closest-to-timestamp order (from the cdx server)
        for cdx in cdx_lines:
            try:
                # optimize: can detect if redirect is needed just from the cdx,
                # no need to load w/arc data if requiring exact match
                if first:
                    redir_response = self._redirect_if_needed(wbrequest, cdx)
                    if redir_response:
                        return redir_response

                    first = False

                response = self.cached_replay_capture(wbrequest,
                                                      cdx,
                                                      cdx_loader,
                                                      failed_files)

            except (CaptureException, ArchiveLoadFailed) as ce:
                # import traceback
                # traceback.print_exc()
                logging.debug(ce)
                last_e = ce
                pass

            if response:
                return response

        if not last_e:
            # can only get here if cdx_lines is empty somehow
            # should be filtered out before hand, but if not
            msg = 'No Captures found for: ' + wbrequest.wb_url.url
            last_e = NotFoundException(msg)

        raise last_e

    def cached_replay_capture(self, wbrequest, cdx, cdx_loader, failed_files):
        def get_capture():
            return self.replay_capture(wbrequest,
                                       cdx,
                                       cdx_loader,
                                       failed_files)

        if not self.enable_range_cache:
            return get_capture()

        range_info = wbrequest.extract_range()

        if not range_info:
            return get_capture()

        range_status, range_iter = (range_cache.
                                    handle_range(wbrequest,
                                                 cdx.get('digest', cdx['urlkey']),
                                                 get_capture,
                                                 *range_info))

        response = self.response_class(range_status,
                                       range_iter,
                                       wbrequest=wbrequest,
                                       cdx=cdx)
        return response

    def replay_capture(self, wbrequest, cdx, cdx_loader, failed_files):
        (status_headers, stream) = (self.content_loader(cdx,
                                                        failed_files,
                                                        cdx_loader,
                                                        wbrequest))

        # check and reject self-redirect
        self._reject_self_redirect(wbrequest, cdx, status_headers)

        # check if redir is needed
        redir_response = self._redirect_if_needed(wbrequest, cdx)
        if redir_response:
            return redir_response

        # length = status_headers.get_header('content-length')
        # stream = LimitReader.wrap_stream(stream, length)

        # one more check for referrer-based self-redirect
        # TODO: evaluate this, as refreshing in browser may sometimes cause
        # referrer to be set to the same page, incorrectly skipping a capture
        # self._reject_referrer_self_redirect(wbrequest)

        urlrewriter = wbrequest.urlrewriter

        # if using url rewriter, use original url for rewriting purposes
        if wbrequest and wbrequest.wb_url:
            wbrequest.wb_url.url = cdx['url']

        head_insert_func = None
        if self.head_insert_view:
            head_insert_func = (self.head_insert_view.
                                create_insert_func(wbrequest))

        result = (self.content_rewriter.
                  rewrite_content(urlrewriter,
                                  status_headers=status_headers,
                                  stream=stream,
                                  head_insert_func=head_insert_func,
                                  urlkey=cdx['urlkey'],
                                  cdx=cdx,
                                  env=wbrequest.env))

        (status_headers, response_iter, is_rewritten) = result

        # buffer response if buffering enabled
        if self.buffer_response:
            content_len = status_headers.get_header('content-length')
            try:
                content_len = int(content_len)
            except:
                content_len = 0

            if content_len <= 0:
                max_size = self.buffer_max_size
                response_iter = self.buffered_response(status_headers,
                                                       response_iter,
                                                       max_size)

        # Set Content-Location if not exact capture
        if not self.redir_to_exact:
            mod = wbrequest.options.get('replay_mod', wbrequest.wb_url.mod)
            canon_url = (wbrequest.urlrewriter.
                         get_new_url(timestamp=cdx['timestamp'],
                                     url=cdx['url'],
                                     mod=mod))

            status_headers.headers.append(('Content-Location', canon_url))

        if wbrequest.wb_url.mod == 'vi_':
            status_headers.headers.append(('access-control-allow-origin', '*'))

        response = self.response_class(status_headers,
                                       response_iter,
                                       wbrequest=wbrequest,
                                       cdx=cdx)

        # notify reporter callback, if any
        if self._reporter:
            self._reporter(wbrequest, cdx, response)

        return response

    # Buffer rewrite iterator and return a response from a string
    def buffered_response(self, status_headers, iterator, max_size):
        out = BytesIO()
        size = 0
        read_all = True

        try:
            for buff in iterator:
                buff = bytes(buff)
                size += len(buff)
                out.write(buff)
                if max_size > 0 and size > max_size:
                    read_all = False
                    break

        finally:
            content = out.getvalue()
            out.close()

        if read_all:
            content_length_str = str(len(content))

            # remove existing content length
            status_headers.replace_header('Content-Length',
                                          content_length_str)
            return [content]
        else:
            status_headers.remove_header('Content-Length')
            return chain(iter([content]), iterator)

    def _redirect_if_needed(self, wbrequest, cdx):
        if not self.redir_to_exact:
            return None

        if wbrequest.options['is_proxy']:
            return None

        if wbrequest.custom_params.get('noredir'):
            return None

        is_timegate = (wbrequest.options.get('is_timegate', False))
        if not is_timegate:
            is_timegate = wbrequest.wb_url.is_latest_replay()

        redir_needed = is_timegate or (cdx['timestamp'] != wbrequest.wb_url.timestamp)

        if not redir_needed:
            return None

        if self.enable_range_cache and wbrequest.extract_range():
            return None

        # if is_timegate:
        #    timestamp = timestamp_now()
        # else:
        timestamp = cdx['timestamp']

        new_url = (wbrequest.urlrewriter.
                   get_new_url(timestamp=timestamp,
                               url=cdx['url']))

        if wbrequest.method == 'POST':
            #   FF shows a confirm dialog, so can't use 307 effectively
            #   was: statusline = '307 Same-Method Internal Redirect'
            return None
        elif is_timegate:
            statusline = '302 Found'
        else:
            # clear cdx line to indicate internal redirect
            statusline = '302 Internal Redirect'
            cdx = None

        status_headers = StatusAndHeaders(statusline,
                                          [('Location', new_url)])

        return self.response_class(status_headers,
                                   wbrequest=wbrequest,
                                   cdx=cdx,
                                   memento_is_redir=True)

    def _reject_self_redirect(self, wbrequest, cdx, status_headers):
        """
        Check if response is a 3xx redirect to the same url
        If so, reject this capture to avoid causing redirect loop
        """
        if not status_headers.statusline.startswith('3'):
            return

        # skip all 304s
        if (status_headers.statusline.startswith('304') and
                not wbrequest.wb_url.is_identity):
            raise CaptureException('Skipping 304 Modified: ' + str(cdx))

        request_url = wbrequest.wb_url.url.lower()
        location_url = status_headers.get_header('Location')
        if not location_url:
            return

        location_url = location_url.lower()
        if location_url.startswith('/'):
            host = urlsplit(cdx['url']).netloc
            location_url = host + location_url

        if (ReplayView.strip_scheme_www(request_url) ==
                ReplayView.strip_scheme_www(location_url)):
            raise CaptureException('Self Redirect: ' + str(cdx))

    # TODO: reevaluate this, as it may reject valid refreshes of a page
    def _reject_referrer_self_redirect(self, wbrequest):  # pragma: no cover
        """
        Perform final check for referrer based self-redirect.
        This method should be called after verifying that
        the request timestamp == capture timestamp

        If referrer is same as current url,
        reject this response and try another capture.
        """
        if not wbrequest.referrer:
            return

        # build full url even if using relative-rewriting
        request_url = (wbrequest.host_prefix +
                       wbrequest.rel_prefix + str(wbrequest.wb_url))

        if (ReplayView.strip_scheme_www(request_url) ==
                ReplayView.strip_scheme_www(wbrequest.referrer)):
            raise CaptureException('Self Redirect via Referrer: ' +
                                   str(wbrequest.wb_url))

    @staticmethod
    def strip_scheme_www(url):
        m = ReplayView.STRIP_SCHEME_WWW.match(url)
        match = m.group(2)
        return match


# end pywb.webapp.replay_views

# begin pywb.webapp.handlers
# =================================================================
class SearchPageWbUrlHandler(WbUrlHandler):

    def __init__(self, config):
        self.search_view = init_view(config, 'search_html')

        self.is_frame_mode = config.get('framed_replay', False)
        self.frame_mod = 'tf_'
        self.replay_mod = ''

        self.response_class = WbResponse

        if self.is_frame_mode:
            # html = config.get('frame_insert_html', 'templates/frame_insert.html')
            # self.search_view = J2TemplateView(html, config.get('jinja_env'))
            self.frame_insert_view = init_view(config, 'frame_insert_html')
            assert (self.frame_insert_view)

            self.banner_html = config.get('banner_html', 'banner.html')

            if config.get('enable_memento', False):
                self.response_class = MementoResponse

            if self.is_frame_mode == 'inverse':
                self.frame_mod = ''
                self.replay_mod = 'mp_'

        else:
            self.frame_insert_view = None
            self.banner_html = None

    def render_search_page(self, wbrequest, **kwargs):
        return self.search_view.render_response(wbrequest=wbrequest,
                                                prefix=wbrequest.wb_prefix,
                                                **kwargs)

    def __call__(self, wbrequest):
        # root search page
        if wbrequest.wb_url_str == '/':
            return self.render_search_page(wbrequest)

        wbrequest.options['replay_mod'] = self.replay_mod
        wbrequest.options['frame_mod'] = self.frame_mod

        # render top level frame if in frame mode
        # (not supported in proxy mode)
        if (self.is_frame_mode and wbrequest.wb_url and
                not wbrequest.wb_url.is_query() and
                not wbrequest.options['is_proxy']):

            if wbrequest.wb_url.mod == self.frame_mod:
                wbrequest.options['is_top_frame'] = True
                return self.get_top_frame_response(wbrequest)
            else:
                wbrequest.options['is_framed'] = True
                wbrequest.final_mod = self.frame_mod
        else:
            wbrequest.options['is_framed'] = False

        try:
            return self.handle_request(wbrequest)
        except NotFoundException as nfe:
            return self.handle_not_found(wbrequest, nfe)

    def get_top_frame_params(self, wbrequest, mod):
        embed_url = wbrequest.wb_url.to_str(mod=mod)

        if wbrequest.wb_url.timestamp:
            timestamp = wbrequest.wb_url.timestamp
        else:
            timestamp = datetime_to_timestamp(datetime.utcnow())

        params = dict(embed_url=embed_url,
                      wbrequest=wbrequest,
                      timestamp=timestamp,
                      url=wbrequest.wb_url.get_url(),
                      banner_html=self.banner_html)

        return params

    def get_top_frame_response(self, wbrequest):
        params = self.get_top_frame_params(wbrequest, mod=self.replay_mod)

        headers = [('Content-Type', 'text/html')]
        status_headers = StatusAndHeaders('200 OK', headers)

        template_result = self.frame_insert_view.render_to_string(**params)
        body = template_result.encode('utf-8')

        return self.response_class(status_headers, [body], wbrequest=wbrequest)


# =================================================================
# Standard WB Handler
# =================================================================
class WBHandler(SearchPageWbUrlHandler):
    def __init__(self, query_handler, config=None):
        super(WBHandler, self).__init__(config)

        self.index_reader = query_handler
        self.not_found_view = init_view(config, 'not_found_html')

        self.replay = self._init_replay_view(config)

        self.fallback_handler = None
        self.fallback_name = config.get('fallback')

    def _init_replay_view(self, config):
        cookie_maker = config.get('cookie_maker')
        record_loader = ArcWarcRecordLoader(cookie_maker=cookie_maker)

        paths = config.get('archive_paths')

        resolving_loader = ResolvingLoader(PathResolverMapper()(paths),
                                           record_loader=record_loader)

        return ReplayView(resolving_loader, config)

    def resolve_refs(self, handler_dict):
        if self.fallback_name:
            self.fallback_handler = handler_dict.get(self.fallback_name)
            logging.debug('Fallback Handler: ' + self.fallback_name)

    def handle_request(self, wbrequest):
        cdx_lines, output = self.index_reader.load_for_request(wbrequest)

        if output != 'text' and wbrequest.wb_url.is_replay():
            return self.handle_replay(wbrequest, cdx_lines)
        else:
            return self.handle_query(wbrequest, cdx_lines, output)

    def handle_query(self, wbrequest, cdx_lines, output):
        return self.index_reader.make_cdx_response(wbrequest,
                                                   cdx_lines,
                                                   output)

    def handle_replay(self, wbrequest, cdx_lines):
        cdx_callback = self.index_reader.cdx_load_callback(wbrequest)

        return self.replay.render_content(wbrequest,
                                          cdx_lines,
                                          cdx_callback)

    def handle_not_found(self, wbrequest, nfe):
        # check fallback: only for replay queries and not for identity
        if (self.fallback_handler and
                not wbrequest.wb_url.is_query() and
                not wbrequest.wb_url.is_identity):
            return self.fallback_handler(wbrequest)

        # if capture query, just return capture page
        if wbrequest.wb_url.is_query():
            output = self.index_reader.get_output_type(wbrequest.wb_url)
            return self.index_reader.make_cdx_response(wbrequest, iter([]), output)
        else:
            return self.not_found_view.render_response(status='404 Not Found',
                                                       wbrequest=wbrequest,
                                                       url=wbrequest.wb_url.url)


# =================================================================
# Static Content Handler
# =================================================================
class StaticHandler(BaseHandler):
    def __init__(self, static_path):
        mimetypes.init()

        self.static_path = static_path
        self.block_loader = LocalFileLoader()

    def __call__(self, wbrequest):
        url = wbrequest.wb_url_str.split('?')[0]
        full_path = self.static_path + url

        try:
            data = self.block_loader.load(full_path)

            data.seek(0, 2)
            size = data.tell()
            data.seek(0)
            headers = [('Content-Length', str(size))]

            if 'wsgi.file_wrapper' in wbrequest.env:
                reader = wbrequest.env['wsgi.file_wrapper'](data)
            else:
                reader = iter(lambda: data.read(), b'')

            content_type = 'application/octet-stream'

            guessed = mimetypes.guess_type(full_path)
            if guessed[0]:
                content_type = guessed[0]

            return WbResponse.bin_stream(reader,
                                         content_type=content_type,
                                         headers=headers)

        except IOError:
            raise NotFoundException('Static File Not Found: ' +
                                    wbrequest.wb_url_str)


# =================================================================
# Debug Handlers
# =================================================================
class DebugEchoEnvHandler(BaseHandler):  # pragma: no cover
    def __call__(self, wbrequest):
        return WbResponse.text_response(str(wbrequest.env))


# =================================================================
class DebugEchoHandler(BaseHandler):  # pragma: no cover
    def __call__(self, wbrequest):
        return WbResponse.text_response(str(wbrequest))


# end pywb.webapp.handlers

# begin pywb.webapp.live_rewrite_handler
# =================================================================
class RewriteHandler(SearchPageWbUrlHandler):
    LIVE_COOKIE = 'pywb.timestamp={0}; max-age=60'

    YT_DL_TYPE = 'application/vnd.youtube-dl_formats+json'

    def __init__(self, config):
        super(RewriteHandler, self).__init__(config)

        proxyhostport = config.get('proxyhostport')

        live_rewriter_cls = config.get('live_rewriter_cls', LiveRewriter)

        self.live_fetcher = live_rewriter_cls(is_framed_replay=self.is_frame_mode,
                                              proxies=proxyhostport)

        self.recording = self.live_fetcher.is_recording()

        self.head_insert_view = HeadInsertView.init_from_config(config)

        self.live_cookie = config.get('live-cookie', self.LIVE_COOKIE)

        self.verify = config.get('verify_ssl', True)

        self.ydl = None

        self._cache = None

    def handle_request(self, wbrequest):
        if wbrequest.wb_url.is_query():
            type_ = wbrequest.wb_url.LATEST_REPLAY
            url = wbrequest.urlrewriter.get_new_url(type=type_, timestamp='')
            return WbResponse.redir_response(url)

        try:
            return self.render_content(wbrequest)

        except Exception as exc:
            import traceback
            err_details = traceback.format_exc()
            print(err_details)

            url = wbrequest.wb_url.url
            msg = 'Could not load the url from the live web: ' + url
            raise LiveResourceException(msg=msg, url=url)

    def _live_request_headers(self, wbrequest):
        return {}

    def _skip_recording(self, wbrequest):
        return False

    def render_content(self, wbrequest):
        if wbrequest.wb_url.mod == 'vi_':
            return self._get_video_info(wbrequest)

        head_insert_func = self.head_insert_view.create_insert_func(wbrequest)
        req_headers = self._live_request_headers(wbrequest)

        ref_wburl_str = wbrequest.extract_referrer_wburl_str()
        if ref_wburl_str:
            wbrequest.env['REL_REFERER'] = WbUrl(ref_wburl_str).url

        skip_recording = self._skip_recording(wbrequest)

        use_206 = False
        url = None
        rangeres = None

        readd_range = False
        cache_key = None

        if self.recording and not skip_recording:
            rangeres = wbrequest.extract_range()

            if rangeres:
                url, start, end, use_206 = rangeres

                # if bytes=0- Range request,
                # simply remove the range and still proxy
                if start == 0 and not end and use_206:
                    wbrequest.wb_url.url = url
                    del wbrequest.env['HTTP_RANGE']
                    readd_range = True
                else:
                    # disables proxy
                    skip_recording = True

                    # sets cache_key only if not already cached
                    cache_key = self._get_cache_key('r:', url)

        result = self.live_fetcher.fetch_request(wbrequest.wb_url.url,
                                                 wbrequest.urlrewriter,
                                                 head_insert_func=head_insert_func,
                                                 req_headers=req_headers,
                                                 env=wbrequest.env,
                                                 skip_recording=skip_recording,
                                                 verify=self.verify)

        wbresponse = self._make_response(wbrequest, *result)

        if readd_range:
            content_length = (wbresponse.status_headers.
                              get_header('Content-Length'))
            try:
                content_length = int(content_length)
                wbresponse.status_headers.add_range(0, content_length,
                                                    content_length)
            except (ValueError, TypeError):
                pass

        if self.recording and cache_key:
            self._add_rec_ping(cache_key, url, wbrequest, wbresponse)

        if rangeres:
            referrer = wbrequest.env.get('REL_REFERER')

            # also ping video info
            if referrer:
                try:
                    resp = self._get_video_info(wbrequest,
                                                info_url=referrer,
                                                video_url=url)
                except:
                    print('Error getting video info')

        return wbresponse

    def _make_response(self, wbrequest, status_headers, gen, is_rewritten):
        # if cookie set, pass recorded timestamp info via cookie
        # so that client side may be able to access it
        # used by framed mode to update frame banner
        if self.live_cookie:
            cdx = wbrequest.env.get('pywb.cdx')
            if cdx:
                value = self.live_cookie.format(cdx['timestamp'])
                status_headers.headers.append(('Set-Cookie', value))

        return WbResponse(status_headers, gen)

    def _get_cache_key(self, prefix, url):
        if not self._cache:
            self._cache = create_cache()

        key = self.create_cache_key(prefix, url)

        if key in self._cache:
            return None

        return key

    @staticmethod
    def create_cache_key(prefix, url):
        hash_ = hashlib.md5()
        hash_.update(url.encode('utf-8'))
        key = hash_.hexdigest()
        key = prefix + key
        return key

    def _add_rec_ping(self, key, url, wbrequest, wbresponse):
        def do_ping():
            headers = self._live_request_headers(wbrequest)
            headers['Connection'] = 'close'

            try:
                # mark as pinged
                self._cache[key] = '1'

                self.live_fetcher.fetch_async(url, headers)

            except:
                del self._cache[key]
                raise

        def wrap_buff_gen(gen):
            for x in gen:
                yield x

            try:
                do_ping()
            except:
                pass

        # do_ping()
        wbresponse.body = wrap_buff_gen(wbresponse.body)
        return wbresponse

    def _get_video_info(self, wbrequest, info_url=None, video_url=None):
        if not video_url:
            video_url = wbrequest.wb_url.url

        if not info_url:
            info_url = wbrequest.wb_url.url

        cache_key = None
        if self.recording:
            cache_key = self._get_cache_key('v:', video_url)

        info = self.live_fetcher.get_video_info(video_url)
        if info is None:  # pragma: no cover
            msg = ('youtube-dl is not installed, pip install youtube-dl to ' +
                   'enable improved video proxy')

            return WbResponse.text_response(text=msg, status='404 Not Found')

        # if info and info.formats and len(info.formats) == 1:

        content_type = self.YT_DL_TYPE
        metadata = json.dumps(info)

        if (self.recording and cache_key):
            headers = self._live_request_headers(wbrequest)
            headers['Content-Type'] = content_type

            if info_url.startswith('https://'):
                info_url = info_url.replace('https', 'http', 1)

            response = self.live_fetcher.add_metadata(info_url, headers, metadata)

            self._cache[cache_key] = '1'

        return WbResponse.text_response(metadata, content_type=content_type)


# end pywb.webapp.live_rewrite_handler

# begin pywb.webapp.cdx_api_handler
# =================================================================
class CDXAPIHandler(BaseHandler):
    """
    Handler which passes wsgi request to cdx server and
    returns a text-based cdx api
    """

    def __init__(self, index_handler):
        self.index_handler = index_handler

    def __call__(self, wbrequest):
        params = self.extract_params_from_wsgi_env(wbrequest.env)

        cdx_iter = self.index_handler.load_cdx(wbrequest, params)

        return WbResponse.text_stream(cdx_iter,
                                      content_type='text/plain')

    @staticmethod
    def extract_params_from_wsgi_env(env):
        """ utility function to extract params and create a CDXQuery
        from a WSGI environment dictionary
        """
        params = parse_qs(env['QUERY_STRING'])

        # parse_qs produces arrays for single values
        # cdx processing expects singleton params for all params,
        # except filters, so convert here
        # use first value of the list
        for name, val in six.iteritems(params):
            if name != 'filter':
                params[name] = val[0]

        if 'output' not in params:
            params['output'] = 'text'
        elif params['output'] not in ('text', 'json'):
            params['output'] = 'text'

        return params


# end pywb.webapp.cdx_api_handler


# begin pywb.webapp.query_handler
# =================================================================
class QueryHandler(object):
    """
    Main interface for querying the index (currently only CDX) from a
    source server (currently a cdx server)

    Creates an appropriate query based on wbrequest type info and outputs
    a returns a view for the cdx, either a raw cdx iter, an html view,
    etc...
    """

    def __init__(self, cdx_server, html_query_view=None, perms_policy=None):
        self.cdx_server = cdx_server
        self.perms_policy = perms_policy

        self.views = {}
        if html_query_view:
            self.views['html'] = html_query_view

        self.views['timemap'] = MementoTimemapView()

    @staticmethod
    def init_from_config(config,
                         ds_rules_file=DEFAULT_RULES_FILE,
                         html_view=None,
                         server_cls=None):

        perms_policy = None

        if hasattr(config, 'get'):
            perms_policy = config.get('perms_policy')
            server_cls = config.get('server_cls', server_cls)

        cdx_server = create_cdx_server(config, ds_rules_file, server_cls)

        return QueryHandler(cdx_server, html_view, perms_policy)

    def get_output_type(self, wb_url):
        # cdx server only supports text and cdxobject for now
        if wb_url.mod == 'cdx_':
            output = 'text'
        elif wb_url.mod == 'timemap':
            output = 'timemap'
        elif wb_url.is_query():
            output = 'html'
        else:
            output = 'cdxobject'

        return output

    def load_for_request(self, wbrequest):
        wbrequest.normalize_post_query()

        wb_url = wbrequest.wb_url
        output = self.get_output_type(wb_url)

        # init standard params
        params = self.get_query_params(wb_url)

        params['allowFuzzy'] = True
        params['url'] = wb_url.url
        params['output'] = output

        params['filter'].append('!mimetype:-')

        # get metadata
        if wb_url.mod == 'vi_':
            # matching metadata explicitly with special scheme
            schema, rest = wb_url.url.split('://', 1)
            params['url'] = 'metadata://' + rest
            params['filter'].append('~original:metadata://')

        cdx_iter = self.load_cdx(wbrequest, params)
        return cdx_iter, output

    def load_cdx(self, wbrequest, params):
        if wbrequest:
            # add any custom filter from the request
            if wbrequest.query_filter:
                filters = params.get('filter')
                if filters:
                    filters.extend(wbrequest.query_filter)
                else:
                    params['filter'] = wbrequest.query_filter

            params['coll'] = wbrequest.coll
            if wbrequest.custom_params:
                params.update(wbrequest.custom_params)

        if self.perms_policy:
            perms_op = make_perms_cdx_filter(self.perms_policy, wbrequest)
            if perms_op:
                params['custom_ops'] = [perms_op]

        cdx_iter = self.cdx_server.load_cdx(**params)
        return cdx_iter

    def make_cdx_response(self, wbrequest, cdx_iter, output, **kwargs):
        # if not text, the iterator is assumed to be CDXObjects
        if output and output != 'text':
            view = self.views.get(output)
            if view:
                return view.render_response(wbrequest, cdx_iter, **kwargs)

        return WbResponse.text_stream(cdx_iter)

    def cdx_load_callback(self, wbrequest):
        def load_cdx(params):
            params['output'] = 'cdxobject'
            return self.load_cdx(wbrequest, params)

        return load_cdx

    def get_query_params(self,
                         wburl, limit=150000,
                         collapse_time=None,
                         replay_closest=100):

        # if wburl.type == wburl.URL_QUERY:
        #    raise NotImplementedError('Url Query Not Yet Supported')

        return {
            wburl.QUERY:
                {'collapseTime': collapse_time,
                 'filter': ['!statuscode:(500|502|504)'],
                 'from': wburl.timestamp,
                 'to': wburl.end_timestamp,
                 'limit': limit,
                 'matchType': 'exact',
                 },

            wburl.URL_QUERY:
                {'collapse': 'urlkey',
                 'matchType': 'prefix',
                 'showGroupCount': True,
                 'showUniqCount': True,
                 'lastSkipTimestamp': True,
                 'limit': limit,
                 'fl': ('urlkey,original,timestamp,' +
                        'endtimestamp,groupcount,uniqcount'),
                 'filter': [],
                 },

            wburl.REPLAY:
                {'sort': 'closest',
                 'filter': ['!statuscode:(500|502|504)'],
                 'limit': replay_closest,
                 'closest': wburl.timestamp,
                 'resolveRevisits': True,
                 'matchType': 'exact',
                 },

            wburl.LATEST_REPLAY:
                {'sort': 'reverse',
                 # Not appropriate as default
                 # Should be an option to configure status code filtering in general
                 #         'filter': ['statuscode:[23]..|-'],
                 'filter': [],
                 'limit': '1',
                 'resolveRevisits': True,
                 'matchType': 'exact',
                 }

        }[wburl.type]


# end pywb.webapp.query_handler

# begin pywb.webapp.pywb_init
# =================================================================
class DictChain(object):
    def __init__(self, *dicts):
        self.dicts = dicts

    def get(self, key, default_val=None):
        for d in self.dicts:
            val = d.get(key)
            if val is not None:
                return val
        return default_val

    def __contains__(self, key):
        return self.get(key) is not None

    def __getitem__(self, key):
        return self.get(key)

    def __setitem__(self, key, value):
        self.dicts[0][key] = value


# =================================================================
def create_wb_handler(query_handler, config):
    wb_handler_class = config.get('wb_handler_class', WBHandler)

    wb_handler = wb_handler_class(
        query_handler,
        config=config,
    )

    return wb_handler


# =================================================================
def create_live_handler(config):
    wb_handler_class = config.get('wb_handler_class', RewriteHandler)

    live_handler = wb_handler_class(config)

    return live_handler


# =================================================================
def init_route_config(value, config):
    if isinstance(value, str) or isinstance(value, list):
        value = dict(index_paths=value)

    route_config = DictChain(value, config)
    return route_config


# =================================================================
def init_collection(route_config):
    ds_rules_file = route_config.get('domain_specific_rules', None)

    html_view = init_view(route_config, 'query_html', J2HtmlCapturesView)

    server_cls = route_config.get('server_cls')

    query_handler = QueryHandler.init_from_config(route_config,
                                                  ds_rules_file,
                                                  html_view,
                                                  server_cls)

    return query_handler


# =================================================================
def add_cdx_api_handler(name, cdx_api_suffix, routes, query_handler,
                        route_class=Route):
    # if bool, use -cdx suffix, else use custom string
    # as the suffix
    if isinstance(cdx_api_suffix, bool):
        name += '-cdx'
    else:
        name += str(cdx_api_suffix)

    logging.debug('Adding CDX API Handler: ' + name)
    routes.append(route_class(name, CDXAPIHandler(query_handler)))


# =================================================================
def create_cdx_server_app(passed_config):
    """
    Create a cdx server api-only app
    For each collection, create a /<coll>-cdx access point
    which follows the cdx api
    """

    defaults = load_yaml_config(DEFAULT_CONFIG)

    config = DictChain(passed_config, defaults)

    collections = config.get('collections', {})

    static_routes = {}

    # collections based on file system
    if config.get('enable_auto_colls', True):
        colls_loader_cls = config.get('colls_loader_cls', DirectoryCollsLoader)
        dir_loader = colls_loader_cls(config, static_routes, collections)
        dir_loader()
        # collections.update(dir_loader())

    routes = []

    for name, value in six.iteritems(collections):
        route_config = init_route_config(value, config)
        query_handler = init_collection(route_config)

        cdx_api_suffix = route_config.get('enable_cdx_api', True)

        add_cdx_api_handler(name, cdx_api_suffix, routes, query_handler)

    return ArchivalRouter(routes)


# =================================================================
class DirectoryCollsLoader(object):
    def __init__(self, config, static_routes, colls):
        self.config = config
        self.static_routes = static_routes
        self.colls = colls

    def __call__(self):
        colls = self.colls

        static_dir = self.config.get('paths')['static_path']
        static_shared_prefix = self.config.get('static_shared_prefix')

        if static_dir and static_shared_prefix and os.path.isdir(static_dir):
            static_dir = os.path.abspath(static_dir) + os.path.sep
            self.static_routes[static_shared_prefix] = static_dir

        root_dir = self.config.get('collections_root', '')
        if not root_dir or not os.path.isdir(root_dir):
            return colls

        for name in os.listdir(root_dir):
            full = os.path.join(root_dir, name)
            if not os.path.isdir(full):
                continue

            coll_config = self.load_coll_dir(full, name)
            if coll_config:
                # if already exists, override existing config with coll specific
                if name in colls:
                    colls[name].update(coll_config)
                else:
                    colls[name] = coll_config

        return colls

    def _norm_path(self, root_dir, path):
        result = os.path.normpath(os.path.join(root_dir, path))
        return result

    def _add_dir_if_exists(self, coll, root_dir, dir_key, required=False):
        curr_val = coll.get(dir_key)
        if curr_val:
            # add collection path only if relative path, and not a url
            if '://' not in curr_val and not os.path.isabs(curr_val):
                coll[dir_key] = self._norm_path(root_dir, curr_val) + os.path.sep
            return False

        thedir = self.config.get('paths')[dir_key]

        fulldir = os.path.join(root_dir, thedir)

        if os.path.isdir(fulldir):
            fulldir = os.path.abspath(fulldir) + os.path.sep
            coll[dir_key] = fulldir
            return True
        elif required:
            msg = 'Dir "{0}" does not exist for "{1}"'.format(fulldir, dir_key)
            raise Exception(msg)
        else:
            return False

    def load_yaml_file(self, root_dir, filename):
        filename = os.path.join(root_dir, filename)
        if os.path.isfile(filename):
            return load_yaml_config(filename)
        else:
            return {}

    def load_coll_dir(self, root_dir, name):
        # Load config.yaml
        coll_config = self.load_yaml_file(root_dir, 'config.yaml')

        # Load metadata.yaml
        metadata = self.load_yaml_file(root_dir, 'metadata.yaml')
        coll_config['metadata'] = metadata

        self._add_dir_if_exists(coll_config, root_dir, 'index_paths', True)

        # inherit these properties from base, in case archive_paths is shared
        shared_config = DictChain(coll_config, self.config)
        self._add_dir_if_exists(shared_config, root_dir, 'archive_paths', True)

        if self._add_dir_if_exists(coll_config, root_dir, 'static_path', False):
            self.static_routes['static/' + name] = coll_config['static_path']

        # Custom templates dir
        templates_dir = self.config.get('paths').get('templates_dir')
        if templates_dir:
            template_dir = os.path.join(root_dir, templates_dir)

        # Check all templates
        template_files = self.config.get('paths')['template_files']
        for tname, tfile in six.iteritems(template_files):
            if tname in coll_config:
                # Already set
                coll_config[tname] = self._norm_path(root_dir, coll_config[tname])

            # If templates override dir
            elif templates_dir:
                full = os.path.join(template_dir, tfile)
                if os.path.isfile(full):
                    coll_config[tname] = full

        return coll_config


# =================================================================
def create_wb_router(passed_config=None):
    passed_config = passed_config or {}

    defaults = load_yaml_config(DEFAULT_CONFIG)

    config = DictChain(passed_config, defaults)

    routes = []

    port = config.get('port')

    collections = config.get('collections', {})

    static_routes = config.get('static_routes', {})

    root_route = None

    # collections based on file system
    if config.get('enable_auto_colls', True):
        colls_loader_cls = config.get('colls_loader_cls', DirectoryCollsLoader)
        dir_loader = colls_loader_cls(config, static_routes, collections)
        dir_loader()
        # collections.update(dir_loader())

    if config.get('enable_memento', False):
        request_class = MementoRequest
    else:
        request_class = WbRequest

    # store live and replay handlers
    handler_dict = {}

    # setup template globals
    templates_dirs = config['templates_dirs']
    jinja_env = J2TemplateView.init_shared_env(paths=templates_dirs,
                                               packages=config['template_packages'])

    jinja_env.globals.update(config.get('template_globals', {}))

    for static_name, static_path in six.iteritems(static_routes):
        routes.append(Route(static_name, StaticHandler(static_path)))

    for name, value in six.iteritems(collections):
        if isinstance(value, BaseHandler):
            handler_dict[name] = value
            new_route = Route(name, value, config=config)
            if name != '':
                routes.append(new_route)
            else:
                root_route = new_route
            continue

        route_config = init_route_config(value, config)
        route_class = route_config.get('route_class', Route)

        if route_config.get('index_paths') == '$liveweb':
            live = create_live_handler(route_config)
            handler_dict[name] = live
            new_route = route_class(name, live, config=route_config)
            if name != '':
                routes.append(new_route)
            else:
                root_route = new_route
            continue

        query_handler = init_collection(route_config)

        wb_handler = create_wb_handler(
            query_handler=query_handler,
            config=route_config,
        )

        handler_dict[name] = wb_handler

        logging.debug('Adding Collection: ' + name)

        new_route = route_class(name, wb_handler,
                                config=route_config,
                                request_class=request_class)

        if name != '':
            routes.append(new_route)
        else:
            root_route = new_route

        # cdx query handler
        cdx_api_suffix = route_config.get('enable_cdx_api', False)

        if cdx_api_suffix:
            add_cdx_api_handler(name, cdx_api_suffix, routes, query_handler,
                                route_class=route_class)

    if config.get('debug_echo_env', False):
        routes.append(Route('echo_env', DebugEchoEnvHandler()))

    if config.get('debug_echo_req', False):
        routes.append(Route('echo_req', DebugEchoHandler()))

    if root_route:
        routes.append(root_route)

    # resolve any cross handler references
    for route in routes:
        if hasattr(route.handler, 'resolve_refs'):
            route.handler.resolve_refs(handler_dict)

    # default to regular archival mode
    router = ArchivalRouter

    if config.get('enable_http_proxy', False):
        router = ProxyArchivalRouter

        view = init_view(config, 'proxy_select_html')

        if 'proxy_options' not in passed_config:
            passed_config['proxy_options'] = {}

        if view:
            passed_config['proxy_options']['proxy_select_view'] = view

        view = init_view(config, 'proxy_cert_download_html')

        if view:
            passed_config['proxy_options']['proxy_cert_download_view'] = view

    # Finally, create wb router
    return router(
        routes,
        port=port,
        abs_path=config.get('absolute_paths', True),
        home_view=init_view(config, 'home_html'),
        error_view=init_view(config, 'error_html'),
        info_view=init_view(config, 'info_json'),
        config=config
    )


# end  pywb.webapp.pywb_init

# begin pywb.framework.wsgi_wrappers
# =================================================================
class WSGIApp(object):
    def __init__(self, wb_router, fallback_app=None):
        self.wb_router = wb_router
        self.fallback_app = fallback_app

    # Top-level wsgi application
    def __call__(self, env, start_response):
        if env['REQUEST_METHOD'] == 'CONNECT':
            return self.handle_connect(env, start_response)
        else:
            return self.handle_methods(env, start_response)

    def handle_connect(self, env, start_response):
        def ssl_start_response(statusline, headers):
            ssl_sock = env.get('pywb.proxy_ssl_sock')
            if not ssl_sock:
                start_response(statusline, headers)
                return

            env['pywb.proxy_statusline'] = statusline

            status_line = 'HTTP/1.1 ' + statusline + '\r\n'
            ssl_sock.write(status_line.encode('iso-8859-1'))

            for name, value in headers:
                line = name + ': ' + value + '\r\n'
                ssl_sock.write(line.encode('iso-8859-1'))

        resp_iter = self.handle_methods(env, ssl_start_response)

        ssl_sock = env.get('pywb.proxy_ssl_sock')
        if not ssl_sock:
            return resp_iter

        ssl_sock.write(b'\r\n')

        for obj in resp_iter:
            if obj:
                ssl_sock.write(obj)
        ssl_sock.close()

        start_response(env['pywb.proxy_statusline'], [])

        return []

    def handle_methods(self, env, start_response):
        wb_router = self.wb_router
        response = None

        try:
            response = wb_router(env)

            if not response:
                if self.fallback_app:
                    return self.fallback_app(env, start_response)
                else:
                    msg = 'No handler for "{0}".'.format(env['REL_REQUEST_URI'])
                    raise NotFoundException(msg)

        except WbException as e:
            response = self.handle_exception(env, e, False)

        except Exception as e:
            response = self.handle_exception(env, e, True)

        return response(env, start_response)

    def handle_exception(self, env, exc, print_trace):
        error_view = None

        if hasattr(self.wb_router, 'error_view'):
            error_view = self.wb_router.error_view

        if hasattr(exc, 'status'):
            status = exc.status()
        else:
            status = '500 Internal Server Error'

        if hasattr(exc, 'url'):
            err_url = exc.url
        else:
            err_url = None

        if len(exc.args):
            err_msg = exc.args[0]

        if print_trace:
            import traceback
            err_details = traceback.format_exc()
            print(err_details)
        else:
            logging.info(err_msg)
            err_details = None

        if error_view:
            if err_url and isinstance(err_url, str):
                err_url = to_native_str(err_url, 'utf-8')
            if err_msg and isinstance(err_msg, str):
                err_msg = to_native_str(err_msg, 'utf-8')

            return error_view.render_response(exc_type=type(exc).__name__,
                                              err_msg=err_msg,
                                              err_details=err_details,
                                              status=status,
                                              env=env,
                                              err_url=err_url)
        else:
            msg = status + ' Error: '
            if err_msg:
                msg += err_msg

            # msg = msg.encode('utf-8', 'ignore')
            return WbResponse.text_response(msg,
                                            status=status)


# =================================================================
def init_app(init_func, load_yaml=True, config_file=None, config=None):
    logging.basicConfig(format='%(asctime)s: [%(levelname)s]: %(message)s',
                        level=logging.DEBUG)
    logging.debug('')

    try:
        config = config or {}
        if load_yaml:
            # env setting overrides all others
            env_config = os.environ.get('PYWB_CONFIG_FILE')
            if env_config:
                config_file = env_config

            if not config_file:
                config_file = DEFAULT_CONFIG_FILE

            if os.path.isfile(config_file):
                config = load_yaml_config(config_file)

        wb_router = init_func(config)
    except:
        msg = '*** pywb app init FAILED config from "%s"!\n'
        logging.exception(msg, init_func.__name__)
        raise
    else:
        msg = '*** pywb app inited with config from "%s"!\n'
        logging.debug(msg, init_func.__name__)

    return WSGIApp(wb_router)


# =================================================================
def start_wsgi_ref_server(the_app, name, port):  # pragma: no cover
    from wsgiref.simple_server import make_server, WSGIServer
    from six.moves.socketserver import ThreadingMixIn

    # disable is_hop_by_hop restrictions
    import wsgiref.handlers
    wsgiref.handlers.is_hop_by_hop = lambda x: False

    if port is None:
        port = DEFAULT_PORT

    logging.info('Starting %s on port %s', name, port)

    class ThreadingWSGIServer(ThreadingMixIn, WSGIServer):
        pass

    try:
        httpd = make_server('', port, the_app, ThreadingWSGIServer)
        httpd.serve_forever()
    except KeyboardInterrupt as ex:
        pass
    finally:
        logging.info('Stopping %s', name)


# end pywb.framework.wsgi_wrappers


# begin pywb.apps.cli
#=================================================================
def cdx_server(args=None):  #pragma: no cover
    CdxCli(args=args,
           default_port=8080,
           desc='pywb CDX Index Server').run()


#=================================================================
def live_rewrite_server(args=None):  #pragma: no cover
    LiveCli(args=args,
            default_port=8090,
            desc='pywb Live Rewrite Proxy Server').run()


#=================================================================
def wayback(args=None):
    WaybackCli(args=args,
               default_port=8080,
               desc='pywb Wayback Web Archive Replay').run()


#=============================================================================
class BaseCli(object):
    def __init__(self, args=None, default_port=8080, desc=''):
        parser = ArgumentParser(desc)
        parser.add_argument('-p', '--port', type=int, default=default_port)
        parser.add_argument('-t', '--threads', type=int, default=4)
        parser.add_argument('-s', '--server')

        self.desc = desc

        self._extend_parser(parser)

        self.r = parser.parse_args(args)

        self.application = self.load()

    def _extend_parser(self, parser):  #pragma: no cover
        pass

    def load(self):  #pragma: no cover
        pass

    def run(self):
        if self.r.server == 'waitress':  #pragma: no cover
            self.run_waitress()
        else:
            self.run_wsgiref()

    def run_waitress(self):  #pragma: no cover
        from waitress import serve
        print(self.desc)
        serve(self.application, port=self.r.port, threads=self.r.threads)

    def run_wsgiref(self):  #pragma: no cover
        start_wsgi_ref_server(self.application, self.desc, port=self.r.port)


#=============================================================================
class LiveCli(BaseCli):
    def _extend_parser(self, parser):
        parser.add_argument('-x', '--proxy',
                            help='Specify host:port to use as HTTP/S proxy')

        parser.add_argument('-f', '--framed', action='store_true',
                            help='Replay using framed wrapping mode')

    def load(self):
        config = dict(proxyhostport=self.r.proxy,
                      framed_replay='inverse' if self.r.framed else False,
                      enable_auto_colls=False,
                      collections={'live': '$liveweb'})

        return init_app(create_wb_router, load_yaml=False, config=config)


#=============================================================================
class ReplayCli(BaseCli):
    def _extend_parser(self, parser):
        parser.add_argument('-a', '--autoindex', action='store_true')

        help_dir='Specify root archive dir (default is current working directory)'
        parser.add_argument('-d', '--directory', help=help_dir)


    def load(self):
        if self.r.directory:  #pragma: no cover
            os.chdir(self.r.directory)

    def run(self):
        if self.r.autoindex:
            m = CollectionsManager('', must_exist=False)
            if not os.path.isdir(m.colls_dir):
                msg = 'No managed directory "{0}" for auto-indexing'
                logging.error(msg.format(m.colls_dir))
                sys.exit(2)
            else:
                msg = 'Auto-Indexing Enabled on "{0}"'
                logging.info(msg.format(m.colls_dir))
                m.autoindex(do_loop=False)

        super(ReplayCli, self).run()

#=============================================================================
class CdxCli(ReplayCli):  #pragma: no cover
    def load(self):
        super(CdxCli, self).load()
        return init_app(create_cdx_server_app,
                        load_yaml=True)


#=============================================================================
class WaybackCli(ReplayCli):
    def load(self):
        super(WaybackCli, self).load()
        return init_app(create_wb_router,
                        load_yaml=True)

# end pywb.apps.cli


# =================================================================
# init pywb app
# =================================================================
#=============================================================================
if __name__ == "__main__":
    multiprocessing.freeze_support()
    cdx_server()
