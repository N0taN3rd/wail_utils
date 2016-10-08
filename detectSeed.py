from pywb.warc.archiveiterator import DefaultRecordParser
from pywb.warc.cdxindexer import get_cdx_writer_cls,SortedCDXWriter
import tempfile
import json
import random


'''
https://github.com/ikreymer/webarchiveplayer/blob/master/archiveplayer/pagedetect.py
'''
class PageDetectWriterMixin(object):
    EMPTY_DIGEST = '3I42H3S6NNFQ2MSVX7XZKYAYSCX5QBYJ'

    def __enter__(self):
        self.pages = []
        self.referers = set()
        self.count = 0

        self.is_guessing = True
        self.num_urls = 0

        return super(PageDetectWriterMixin, self).__enter__()

    def _possible_page(self, url, ts):
        # try some heuristics to determine if page

        # check for very long query, greater than the rest of url -- probably not a page
        parts = url.split('?', 1)
        if len(parts) == 2 and len(parts[1]) > len(parts[0]):
            return

        # skip robots.txt
        if parts[0].endswith('/robots.txt'):
            return

        self.pages.append(dict(url=url, timestamp=ts))

    def update_metadata(self, metadata, max_pages=500):
        if len(self.pages) >= max_pages:
            metadata['pages'] = random.sample(self.pages, max_pages)
        else:
            metadata['pages'] = self.pages

        metadata['num_urls'] = self.count

    def write(self, entry, filename):
        if entry.record.rec_type in ('response', 'revisit', 'resource'):
            self.count = self.count + 1

        if entry.record.rec_type == 'request':
            return

        # if warcinfo is first, attempt to extract page info
        if entry.record.rec_type == 'warcinfo':
            if self.parse_page_info(entry):
                self.is_guessing = False
            return

        elif entry.record.content_type == 'application/warc-fields':
            return

        # if not guessing, just pass to super
        if self.is_guessing:
            # explicitly add all resource records (for now)
            if entry.record.rec_type == 'resource':
                if (entry['mime'] in ('text/html', 'text/plain') and
                    entry['digest'] != self.EMPTY_DIGEST):
                    self.pages.append(dict(url=entry['url'], timestamp=entry['timestamp']))

            elif (entry['mime'] in ('text/html', 'text/plain')  and
                entry['status'] == '200' and
                entry['digest'] != self.EMPTY_DIGEST):

                self._possible_page(entry['url'], entry['timestamp'])

            elif entry['url'] in self.referers:
                self._possible_page(entry['url'], entry['timestamp'])

            if entry.get('_referer'):
                self.referers.add(entry['_referer'])

        super(PageDetectWriterMixin, self).write(entry, filename)

    def parse_page_info(self, entry):
        #if (entry.record.content_type != 'application/warc-fields'):
        #    return False

        metadata = self.extract_metadata(entry['_warcinfo'])
        if not metadata:
            return False

        self.pages.extend(metadata.get('pages', []))
        self.num_urls += metadata.get('num_urls', 0)
        return True

    @staticmethod
    def extract_metadata(buff):
        buff = buff.decode('utf-8')
        for line in buff.split('\n'):
            parts = line.split(': ', 1)
            if parts[0] != 'json-metadata':
                continue

            try:
                metadata = json.loads(parts[1])
                return metadata
            except Exception as exc:
                import traceback
                err_details = traceback.format_exc()
                print(err_details)

                print('error parsing metadata: ', parts[1])
                continue


class PageDetectSortedWriter(PageDetectWriterMixin, SortedCDXWriter):
    pass


def detect_seed(the_file):
    options = dict(sort=True,
                   surt_ordered=True,
                   append_post=True,
                   cdxj=True,
                   include_all=True,
                   writer_add_mixin=True)
    options['writer_cls'] = PageDetectSortedWriter
    writer_cls = get_cdx_writer_cls(options)
    record_iter = DefaultRecordParser(**options)

    with writer_cls(tempfile.NamedTemporaryFile(delete=True, suffix='.cdxj', prefix='cdx')) as writer:
        with open(the_file, 'rb') as infile:
            entry_iter = record_iter(infile)
            for entry in entry_iter:
                writer.write(entry, 't')
    return writer.pages

