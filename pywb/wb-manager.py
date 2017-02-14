import base64
import brotli
import calendar
import cgi
import codecs
import collections
import datetime
import hashlib
import heapq
import hmac
import logging
import os
import pkg_resources
import re
import requests
import shutil
import six
import surt
import sys
import time
import yaml
import zlib
import multiprocessing
from distutils.util import strtobool
from pkg_resources import resource_string

from argparse import ArgumentParser, RawTextHelpFormatter

from six.moves.urllib.parse import urlencode, quote
from six.moves.urllib.parse import parse_qs
from six.moves.urllib.request import pathname2url, url2pathname
from six.moves.urllib.parse import urljoin, unquote_plus, urlsplit
import six.moves.urllib.parse as urlparse
from six.moves import map
from six.moves import zip
from six.moves import range
from six import iteritems
from six import StringIO

from pprint import pformat
from copy import copy

from bisect import insort

from email.utils import parsedate, formatdate

from watchdog.observers import Observer
from watchdog.events import RegexMatchingEventHandler

from io import open, BytesIO

from json import loads as json_decode

from pywb import DEFAULT_CONFIG


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



# =================================================================
# str <-> datetime conversion
# =================================================================

DATE_TIMESPLIT = re.compile(r'[^\d]')

TIMESTAMP_14 = '%Y%m%d%H%M%S'
ISO_DT = '%Y-%m-%dT%H:%M:%SZ'

PAD_14_DOWN = '10000101000000'
PAD_14_UP = '29991231235959'
PAD_6_UP = '299912'

# =============================================================================
EXT_REGEX = '.*\.w?arc(\.gz)?$'

keep_running = True

# =================================================================
ArcWarcRecord = collections.namedtuple('ArcWarcRecord',
                                       'format, rec_type, rec_headers, ' +
                                       'stream, status_headers, ' +
                                       'content_type, length')

WRAP_WIDTH = 80

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
class WbException(Exception):
    def __init__(self, msg=None, url=None):
        Exception.__init__(self, msg)
        self.msg = msg
        self.url = url


# Default Error Code
#    def status(self):
#        return '500 Internal Server Error'


# =================================================================
class AccessException(WbException):
    def status(self):
        return '403 Access Denied'


# =================================================================
class BadRequestException(WbException):
    def status(self):
        return '400 Bad Request'


# =================================================================
class NotFoundException(WbException):
    def status(self):
        return '404 Not Found'


# =================================================================
class LiveResourceException(WbException):
    def status(self):
        return '400 Bad Live Resource'


# =================================================================
class CDXException(WbException):
    def status(self):
        return '400 Bad Request'


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
        post_query = pyamf_parse(post_query, environ)

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


# =================================================================
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
        # if self.reader.decompressor:
        self.next_line, empty_size = self._consume_blanklines()

        self.offset = self.fh.tell() - self.reader.rem_length()
        # if self.offset < 0:
        #    raise Exception('Not Gzipped Properly')

        if self.next_line:
            self.offset -= len(self.next_line)

        length = self.offset - curr_offset

        if not self.reader.decompressor:
            length -= empty_size

        self.member_info = (curr_offset, length)
        # return self.member_info
        # return next_line

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


# =================================================================
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


# =================================================================
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

    # =================================================================
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

    # =================================================================
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


# =================================================================
class BaseCDXWriter(object):
    def __init__(self, out):
        self.out = codecs.getwriter('utf-8')(out)
        # self.out = out

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


# =================================================================
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


# =================================================================
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


# =================================================================
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


# =================================================================
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


# =================================================================
ALLOWED_EXT = ('.arc', '.arc.gz', '.warc', '.warc.gz')


# =================================================================
def _resolve_rel_path(path, rel_root):
    path = os.path.relpath(path, rel_root)
    if os.path.sep != '/':  # pragma: no cover
        path = path.replace(os.path.sep, '/')
    return path


# =================================================================
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


# =================================================================
def remove_ext(filename):
    for ext in ALLOWED_EXT:
        if filename.endswith(ext):
            filename = filename[:-len(ext)]
            break

    return filename


# =================================================================
def cdx_filename(filename):
    return remove_ext(filename) + '.cdx'


# =================================================================
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


# =================================================================
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


# =================================================================
def write_cdx_index(outfile, infile, filename, **options):
    # filename = filename.encode(sys.getfilesystemencoding())

    writer_cls = get_cdx_writer_cls(options)

    with writer_cls(outfile) as writer:
        entry_iter = DefaultRecordParser(**options)(infile)

        for entry in entry_iter:
            writer.write(entry, filename)

    return writer

# =============================================================================
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


# =============================================================================
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


# ============================================================================
BlockLoader.init_default_loaders()


# =============================================================================
# to allow testing by mocking get_input
def get_input(msg):  # pragma: no cover
    return raw_input(msg)


# =============================================================================
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
        # os.rename(merged_file, cdx_file)
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


# =============================================================================
def main(args=None):
    description = """
Create manage file based web archive collections
"""
    # format(os.path.basename(sys.argv[0]))

    logging.basicConfig(format='%(asctime)s: [%(levelname)s]: %(message)s',
                        level=logging.DEBUG)

    parser = ArgumentParser(description=description,
                            # epilog=epilog,
                            formatter_class=RawTextHelpFormatter)

    subparsers = parser.add_subparsers(dest='type')

    # Init Coll
    def do_init(r):
        m = CollectionsManager(r.coll_name, must_exist=False)
        m.add_collection()

    init_help = 'Init new collection, create all collection directories'
    init = subparsers.add_parser('init', help=init_help)
    init.add_argument('coll_name')
    init.set_defaults(func=do_init)

    # List Colls
    def do_list(r):
        m = CollectionsManager('', must_exist=False)
        m.list_colls()

    list_help = 'List Collections'
    listcmd = subparsers.add_parser('list', help=list_help)
    listcmd.set_defaults(func=do_list)

    # Add Warcs
    def do_add(r):
        m = CollectionsManager(r.coll_name)
        m.add_warcs(r.files)

    addwarc_help = 'Copy ARCS/WARCS to collection directory and reindex'
    addwarc = subparsers.add_parser('add', help=addwarc_help)
    addwarc.add_argument('coll_name')
    addwarc.add_argument('files', nargs='+')
    addwarc.set_defaults(func=do_add)

    # Reindex All
    def do_reindex(r):
        m = CollectionsManager(r.coll_name)
        m.reindex()

    reindex_help = 'Re-Index entire collection'
    reindex = subparsers.add_parser('reindex', help=reindex_help)
    reindex.add_argument('coll_name')
    reindex.set_defaults(func=do_reindex)

    # Index warcs
    def do_index(r):
        m = CollectionsManager(r.coll_name)
        m.index_merge(r.files, m.DEF_INDEX_FILE)

    indexwarcs_help = 'Index specified ARC/WARC files in the collection'
    indexwarcs = subparsers.add_parser('index', help=indexwarcs_help)
    indexwarcs.add_argument('coll_name')
    indexwarcs.add_argument('files', nargs='+')
    indexwarcs.set_defaults(func=do_index)

    # Set metadata
    def do_metadata(r):
        m = CollectionsManager(r.coll_name)
        m.set_metadata(r.set)

    metadata_help = 'Set Metadata'
    metadata = subparsers.add_parser('metadata', help=metadata_help)
    metadata.add_argument('coll_name')
    metadata.add_argument('--set', nargs='+')
    metadata.set_defaults(func=do_metadata)

    # Add default template
    def do_add_template(r):
        m = CollectionsManager(r.coll_name, must_exist=False)
        if r.add:
            m.add_template(r.add, r.force)
        elif r.remove:
            m.remove_template(r.remove, r.force)
        elif r.list:
            m.list_templates()

    template_help = 'Add default html template for customization'
    template = subparsers.add_parser('template', help=template_help)
    template.add_argument('coll_name', nargs='?', default='')
    template.add_argument('-f', '--force', action='store_true')
    template.add_argument('--add')
    template.add_argument('--remove')
    template.add_argument('--list', action='store_true')
    template.set_defaults(func=do_add_template)

    # Migrate CDX
    def do_migrate(r):
        m = CollectionsManager('', must_exist=False)
        m.migrate_cdxj(r.path, r.force)

    migrate_help = 'Convert any existing archive indexes to new json format'
    migrate = subparsers.add_parser('cdx-convert', help=migrate_help)
    migrate.add_argument('path', default='./', nargs='?')
    migrate.add_argument('-f', '--force', action='store_true')
    migrate.set_defaults(func=do_migrate)

    # Auto Index
    def do_autoindex(r):
        m = CollectionsManager(r.coll_name, must_exist=False)
        m.autoindex(True)

    autoindex_help = 'Automatically index any change archive files'
    autoindex = subparsers.add_parser('autoindex', help=autoindex_help)
    autoindex.add_argument('coll_name', nargs='?', default='')
    autoindex.set_defaults(func=do_autoindex)

    r = parser.parse_args(args=args)
    r.func(r)


# special wrapper for cli to avoid printing stack trace
def main_wrap_exc():  # pragma: no cover
    try:
        main()
    except Exception as e:
        print('Error: ' + str(e))
        sys.exit(2)


if __name__ == "__main__":
    multiprocessing.freeze_support()
    main_wrap_exc()
