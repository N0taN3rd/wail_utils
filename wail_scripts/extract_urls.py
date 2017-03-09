import os
import ujson as json
from argparse import ArgumentParser, ArgumentTypeError, Action
from pywb.utils.canonicalize import unsurt
from pywb.warc.cdxindexer import iter_file_or_dir
from pywb.warc.archiveiterator import DefaultRecordParser


class FullPaths(Action):
    def __call__(self, parser, namespace, values, option_string=None):
        setattr(namespace, self.dest, os.path.abspath(os.path.expanduser(values)))


def is_dir(dirname):
    if not os.path.isdir(dirname):
        msg = "{0} is not a directory".format(dirname)
        raise ArgumentTypeError(msg)
    else:
        return dirname


def is_file(path):
    if not os.path.isfile(path):
        msg = "{0} is not a file".format(path)
        raise ArgumentTypeError(msg)
    else:
        return path


def extract_warc(path):

    entries = {}
    for entry in DefaultRecordParser().open(path):
        if "text/html" in entry['mime']:
            url = unsurt('%s)/' % entry['urlkey'].split(')')[0])
            if entries.get(url, None) is None:
                entries[url] = []
            entries[url].append(unsurt(entry['urlkey']))

    return entries


def do_extraction(path):
    results = []
    for path, fname in iter_file_or_dir([path]):
        try:
            result = extract_warc(path)
            results.append({
                'wasError': False,
                'result': result,
                'file': fname
            })
        except Exception as e:
            results.append({
                'wasError': True,
                'result': str(e),
                'file': fname
            })
    print(json.dumps(results))


if __name__ == '__main__':
    parser = ArgumentParser(description="Extract Urls from a warc file", prog='extract_urls',
                            usage='%(prog)s [options]')
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('-d', help='directory containing warc files', action=FullPaths, type=is_dir)
    mode.add_argument('-f', help='a warc file to extract', action=FullPaths, type=is_file)

    args = parser.parse_args()
    if args.d is not None:
        do_extraction(args.d)
    else:
        do_extraction(args.f)
