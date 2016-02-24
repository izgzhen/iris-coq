#!/usr/bin/env python3
import argparse, sys, pprint
import matplotlib.pyplot as plt
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

results = list(parse_log.parse(log_file, args.timings))

for timing in args.timings:
    plt.plot(list(map(lambda r: r.times[timing], results)))

plt.legend(args.timings)
plt.xticks(range(len(results)), list(map(lambda r: r.commit[:7], results)), rotation=70)
plt.subplots_adjust(bottom=0.2) # more space for the commit labels

plt.xlabel('Commit')
plt.ylabel('Time (s)')
plt.title('Time to compile files')
plt.grid(True)
plt.show()
