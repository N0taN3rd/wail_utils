import os
import ujson as json
from argparse import ArgumentParser, ArgumentTypeError, Action

from pywb.warc.archiveiterator import DefaultRecordParser
from pywb.warc.cdxindexer import iter_file_or_dir
from warctools.warc import  WarcRecord


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


def check_warc(path):
    for entry in DefaultRecordParser().open(path):
        it = entry


def do_check(path):
    ret = []
    for path, fname in iter_file_or_dir([path]):
        try:
            check_warc(path)
        except Exception as e:
            print(e)
            ret.append({'error': str(e), 'file': path})
            print(path)
            continue
    print(json.dumps(ret))


def do_check2(path):
    for path, fname in iter_file_or_dir([path]):
        print(path)
        wr = WarcRecord.open_archive(path,gzip='auto')
        try:
            for (offset, record, errors) in wr.read_records(limit=None):
                if errors:
                    print("warc errors at %s:%d" % (fname, offset))
                    print(errors)
                    correct = False

                    break
                elif record is not None and record.validate():  # ugh name, returns errorsa
                    print("warc errors at %s:%d" % (fname, offset))
                    print(record.validate())
                    correct = False
                    break
                it = 1
        except Exception as e:
                print("Exception: %s" % (str(e)))
                correct = False
        finally:
            if wr: wr.close()
            # print(offset,record,errors)
        print('-------------------------------------')



if __name__ == '__main__':
    parser = ArgumentParser(description="Check an archive or warc file for invalid records", prog='extract_urls',
                            usage='%(prog)s [options]')
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('-d', help='directory containing warc files', action=FullPaths, type=is_dir)
    mode.add_argument('-f', help='a warc file to extract', action=FullPaths, type=is_file)

    args = parser.parse_args()
    if args.d is not None:
        do_check2(args.d)
    else:
        do_check2(args.f)
