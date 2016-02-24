import re

class Result:
    def __init__(self, commit, times):
        self.commit = commit
        self.times = times

def parse(file, filter):
    '''[file] should be a file-like object, an iterator over the lines. filter should support "in" queries.
       yields a list of Result objects giving the times of those Coq files that are "in" filter.'''
    commit_re = re.compile("^# ([a-z0-9]+)$")
    time_re = re.compile("^([a-zA-Z0-9_/-]+) \(user: ([0-9.]+) mem: ([0-9]+) ko\)$")
    commit = None
    times = None
    for line in file:
        # next commit?
        m = commit_re.match(line)
        if m is not None:
            # previous commit, if any, is done now
            if times is not None:
                yield Result(commit, times)
            # start recording next commit
            commit = m.group(1)
            times = {} # reset the recorded times
            continue
        # next file time?
        m = time_re.match(line)
        if m is not None:
            name = m.group(1)
            time = float(m.group(2))
            if name in filter:
                times[name] = time
            continue
        # nothing else we know about
        raise Exception("Unexpected line: {}".format(line))
    # end of file. previous commit, if any, is done now.
    if times is not None:
        yield Result(commit, times)
