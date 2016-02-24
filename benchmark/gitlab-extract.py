#!/usr/bin/env python3
import argparse, pprint
import requests

def first(it):
    for i in it:
        return i
    raise Exception("The iterator is empty")

def req(path):
    url = '%s/api/v3/%s' % (args.server, path)
    return requests.get(url, headers={'PRIVATE-TOKEN': args.private_token}).json()

# read command-line arguments
parser = argparse.ArgumentParser(description='Update and build a bunch of stuff')
parser.add_argument("-t", "--private-token",
                    dest="private_token", required=True,
                    help="The private token used to authenticate access")
parser.add_argument("-s", "--server",
                    dest="server", default="https://gitlab.mpi-sws.org/",
                    help="The GitLab server to contact")
parser.add_argument("-p", "--project",
                    dest="project", default="FP / iris-coq",
                    help="The name of the project on GitLab")
args = parser.parse_args()
pp = pprint.PrettyPrinter(indent=4)

projects = req("projects")
project = first(filter(lambda p: p['name_with_namespace'] == args.project, projects))

commit = "7e49776c0b3565364823665ab11ee91ed95ade63"

build = first(sorted(req("/projects/{}/repository/commits/{}/builds".format(project['id'], commit)), key = lambda b: -int(b['id'])))
print("The build ID is {}".format(build['id']))
print(requests.get("{}/{}/builds/{}/artifacts/file/build-time.txt".format(args.server, args.project.replace(' ', ''), build['id'])).text)
