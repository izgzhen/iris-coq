#!/usr/bin/env python3
import argparse, sys, pprint
import parse_log

# read command-line arguments
parser = argparse.ArgumentParser(description='Visualize iris-coq build times')
parser.add_argument("-f", "--file",
                    dest="file", required=True,
                    help="Filename to get the data from.")
parser.add_argument("-t", "--timings", nargs='+',
                    dest="timings",
                    help="The names of the Coq files (without the extension) whose timings should be extracted")
args = parser.parse_args()
pp = pprint.PrettyPrinter()
log_file = sys.stdin if args.file == "-" else open(args.file, "r")

for result in parse_log.parse(log_file, args.timings):
    pp.pprint(result.commit)
    pp.pprint(result.times)
    print()
