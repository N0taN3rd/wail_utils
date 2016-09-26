import os
from requests import request
from collections import defaultdict
from pywb.utils.canonicalize import canonicalize, unsurt
from pywb.warc.recordloader import ArcWarcRecordLoader
from pywb.cdx.cdxobject import CDXObject, ORIGINAL, MIMETYPE, TIMESTAMP
from pywb.warc.cdxindexer import iter_file_or_dir
from pywb.warc.archiveiterator import DefaultRecordParser
import ujson as json


def convert_domain_uri(d, uris):
    out = []
    for k, v in uris.items():
        out.append({"uri": k, "timestamp": v})
    return {"domain": d, "uris": out}


def cdx_mapper(uris):
    return map(lambda x: convert_domain_uri(x[0], x[1]), uris.items())


def warc_mapper(warc_entries):
    entries = {}
    for entry in warc_entries:
        print(entry)
        if "text/html" in entry['mime']:
            edict = {
                "url": entry['url'],
                "status": entry['status'],
                "timestamp": entry['timestamp']
            }
            # entries.append(edict)
            url = unsurt('%s)/' % entry['urlkey'].split(')')[0])
            if entries.get(url, None) is None:
                entries[url] = defaultdict(list)
            entries[url][entry['url']].append(edict)
    return entries

class Lister(object):
    def __init__(self, post_to, identifier):
        self.post_to = post_to
        self.identifier = identifier

    def check(self):
        raise NotImplementedError('Implement in subclass')

    def report_list(self):
        raise NotImplementedError('Implement in subclass')

    def post(self,send):
        print(send)


class ListFromCdxDir(Lister):
    def __init__(self, post_to, identifier, _dir):
        super(ListFromCdxDir, self).__init__(post_to=post_to, identifier=identifier)
        self.dir = _dir

    def iter_cdx_files(self):
        for root, dirs, files in os.walk(self.dir):
            for filename in files:
                if filename.endswith('.cdx'):
                    full_path = os.path.join(root, filename)
                    yield full_path

    def check(self):
        count = 0
        for x in self.iter_cdx_files():
            count += 1
        return count > 0

    def report_list(self):
        cdxFiles = []
        for filename in self.iter_cdx_files():
            uris = {}
            with open(filename, 'rb') as fh:
                for line in fh:
                    if line.startswith(b' CDX'):
                        continue
                    cdx = CDXObject(line)
                    if cdx[MIMETYPE] == 'text/html':
                        surted = canonicalize(cdx[ORIGINAL])
                        url = unsurt('%s)/' % surted.split(')')[0])
                        if uris.get(url, None) is None:
                            uris[url] = defaultdict(list)
                        uris[url][cdx[ORIGINAL]].append(cdx[TIMESTAMP])
            cdxFiles.append({"file": filename, "contents": sorted(cdx_mapper(uris), key=lambda x: x['domain'])})
        for it in cdxFiles:
            print(it)
        self.post(json.dumps(cdxFiles))


class ListFromCdxFile(Lister):
    def __init__(self, post_to, identifier, _file):
        super(ListFromCdxFile, self).__init__(post_to=post_to, identifier=identifier)
        self.file = _file

    def check(self):
        filename, file_extension = os.path.splitext(self.file)
        return os.path.exists(self.file) and ('cdx' in file_extension)

    def report_list(self):
        uris = {}
        with open(self.file, 'rb') as fh:
            for line in fh:
                if line.startswith(b' CDX'):
                    continue
                cdx = CDXObject(line)
                if cdx[MIMETYPE] == 'text/html':
                    surted = canonicalize(cdx[ORIGINAL])
                    url = unsurt('%s)/' % surted.split(')')[0])
                    if uris.get(url, None) is None:
                        uris[url] = defaultdict(list)
                    uris[url][cdx[ORIGINAL]].append(cdx[TIMESTAMP])

        it = {"file": self.file, "contents": sorted(cdx_mapper(uris), key=lambda x: x['domain'])}
        self.post(json.dumps(it))


class ListFromWarc(Lister):
    def __init__(self, post_to, identifier, path):
        super(ListFromWarc, self).__init__(post_to=post_to, identifier=identifier)
        self.path = path

    def check(self):
        counter = 0
        for _ in iter_file_or_dir([self.path]):
            counter += 1
        return counter > 0

    def report_list(self):
        parsed_warcs = []
        for path, fname in iter_file_or_dir([self.path]):
            print(fname)
            reader = DefaultRecordParser(sort=True, append_post=True)(
                open(path, 'rb'))
            parsed_warcs.append({"path": path,"fname": fname,"contents": warc_mapper(reader)})
        if len(parsed_warcs) > 1:
            print('more yay')
            self.post(json.dumps(parsed_warcs))
        else:
            print('1')
            self.post(json.dumps(parsed_warcs[0]))


class ListUrisFromCdxDir(object):
    def __init__(self, dir_):
        self.cdx_dir = dir_

    def iter_cdx_files(self):
        print('iter_cdx_files', self.cdx_dir)
        for root, dirs, files in os.walk(self.cdx_dir):
            print(root, dirs, files)
            for filename in files:
                print(filename)
                if filename.endswith('.cdx'):
                    full_path = os.path.join(root, filename)
                    yield full_path

    def count_cdx(self):
        count = 0
        for x in self.iter_cdx_files():
            count += 1
        return count

    def mapper(self, uris):
        return map(lambda x: convert_domain_uri(x[0], x[1]), uris.items())

    def convert_to_cdxj(self):
        uris = {}
        for filename in self.iter_cdx_files():
            outfile = filename + 'j'

            print('Converting {0} -> {1}'.format(filename, outfile))
            lines = []
            with open(filename, 'rb') as fh:
                for line in fh:
                    if line.startswith(b' CDX'):
                        continue
                    cdx = CDXObject(line)
                    if cdx[MIMETYPE] == 'text/html':
                        surted = canonicalize(cdx[ORIGINAL])
                        url = unsurt('%s)/' % surted.split(')')[0])
                        if uris.get(url, None) is None:
                            uris[url] = defaultdict(list)
                        uris[url][cdx[ORIGINAL]].append(cdx[TIMESTAMP])
        for it in sorted(self.mapper(uris), key=lambda x: x['domain']):
            print(it)


if __name__ == '__main__':
    # lister = ListUrisFromCdxDir('/home/john/my-fork-wail/archiveIndexes/onlyIndex')
    # lister.convert_to_cdxj()
    # warcReader = ArcWarcRecordLoader()
    # rec = warcReader.load('/home/john/my-fork-wail/archives/MAT-20160725182544870-00000-5931~misanthropy~8443.warc
    # ',offset=0,length=-1)

    warcer = ListFromWarc(post_to=None, identifier=None,
                          path='/home/john/my-fork-wail/archives2/collections/Wail/archive/MAT-20160725182544870-00000-5931~misanthropy~8443.warc')
    warcer.report_list()
    # reader = DefaultRecordParser(sort=True, append_post=True)(
    #     open('/home/john/my-fork-wail/archives/MAT-20160725182544870-00000-5931~misanthropy~8443.warc', 'rb'))
    # for entry in reader:
    #     print(entry)
