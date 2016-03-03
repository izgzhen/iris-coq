#!/usr/bin/env python3
import argparse, pprint, sys
import requests
import parse_log

def last(it):
    r = None
    for i in it:
        r = i
    return r

def first(it):
    for i in it:
        return i
    return None

def req(path):
    url = '%s/api/v3/%s' % (args.server, path)
    return requests.get(url, headers={'PRIVATE-TOKEN': args.private_token})

# read command-line arguments
parser = argparse.ArgumentParser(description='Extract iris-coq build logs from GitLab')
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

# determine commit, if missing
if args.commits is None:
    if args.file == "-":
        raise Exception("If you do not give explicit commits, you have to give a logfile so that we can determine the missing commits.")
    last_result = last(parse_log.parse(open(args.file, "r"), parse_times = False))
    args.commits = "{}..origin/master".format(last_result.commit)

projects = req("projects")
project = first(filter(lambda p: p['path_with_namespace'] == args.project, projects.json()))
if project is None:
    sys.stderr.write("Project not found.\n")
    sys.exit(1)

for commit in parse_log.parse_git_commits(args.commits):
    print("Fetching {}...".format(commit))
    commit_data = req("/projects/{}/repository/commits/{}".format(project['id'], commit))
    if commit_data.status_code != 200:
        raise Exception("Commit not found?")
    builds = req("/projects/{}/repository/commits/{}/builds".format(project['id'], commit))
    if builds.status_code != 200:
        # no build
        continue
    build = first(sorted(builds.json(), key = lambda b: -int(b['id'])))
    assert build is not None
    if build['status'] == 'failed':
        # build failed
        continue
    # now fetch the build times
    build_times = requests.get("{}/builds/{}/artifacts/file/build-time.txt".format(project['web_url'], build['id']))
    if build_times.status_code != 200:
        raise Exception("No artifact at build?")
    # Output in the log file format
    log_file.write("# {}\n".format(commit))
    log_file.write(build_times.text)
    log_file.flush()
