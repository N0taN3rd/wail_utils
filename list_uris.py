import os
from  detectSeed import detect_seed
from argparse import ArgumentParser, ArgumentTypeError, Action
from pywb.warc.cdxindexer import iter_file_or_dir

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


def lister(path):
    ret = []
    for path, fname in iter_file_or_dir([path]):
        try:
            ret.append({'name': fname, 'seeds': detect_seed(path)})
        except Exception as e:
            print(e)
            ret.append({'error': str(e), 'file': path})
            print(path)
            continue
    for it in ret:
        print(it)


if __name__ == '__main__':
    parser = ArgumentParser(description="Check an archive or warc file for invalid records", prog='list_urls',
                            usage='%(prog)s [options]')
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('-d', help='directory containing warc files', action=FullPaths, type=is_dir)
    mode.add_argument('-f', help='a warc file to extract urls from', action=FullPaths, type=is_file)

    args = parser.parse_args()
    if args.d is not None:
        lister(args.d)
    else:
        lister(args.f)
