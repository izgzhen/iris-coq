#!/usr/bin/env python3
import argparse, pprint, subprocess, sys
import requests

def first(it):
    for i in it:
        return i
    raise Exception("The iterator is empty")

def req(path):
    url = '%s/api/v3/%s' % (args.server, path)
    return requests.get(url, headers={'PRIVATE-TOKEN': args.private_token})

# read command-line arguments
parser = argparse.ArgumentParser(description='Update and build a bunch of stuff')
parser.add_argument("-t", "--private-token",
                    dest="private_token", required=True,
                    help="The private token used to authenticate access.")
parser.add_argument("-s", "--server",
                    dest="server", default="https://gitlab.mpi-sws.org/",
                    help="The GitLab server to contact.")
parser.add_argument("-p", "--project",
                    dest="project", default="FP/iris-coq",
                    help="The name of the project on GitLab.")
parser.add_argument("-f", "--file",
                    dest="file", required=True,
                    help="Filename to store the load in.")
parser.add_argument("-c", "--commits",
                    dest="commits",
                    help="The commits to fetch. Default is everything since the most recent entry in the log file.")
args = parser.parse_args()
log_file = sys.stdout if args.file == "-" else open(args.file, "a")

projects = req("projects")
project = first(filter(lambda p: p['path_with_namespace'] == args.project, projects.json()))

if args.commits.find('..') >= 0:
    # a range of commits
    commits = subprocess.check_output(["git", "rev-list", args.commits]).decode("utf-8")
else:
    # a single commit
    commits = subprocess.check_output(["git", "rev-parse", args.commits]).decode("utf-8")
for commit in reversed(commits.strip().split('\n')):
    print("Fetching {}...".format(commit))
    builds = req("/projects/{}/repository/commits/{}/builds".format(project['id'], commit))
    if builds.status_code != 200:
        continue
    try:
        build = first(sorted(builds.json(), key = lambda b: -int(b['id'])))
    except Exception:
        # no build
        continue
    build_times = requests.get("{}/builds/{}/artifacts/file/build-time.txt".format(project['web_url'], build['id']))
    if build_times.status_code != 200:
        continue
    # Output in the log file format
    log_file.write("# {}\n".format(commit))
    log_file.write(build_times.text)
