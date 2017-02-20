#!/bin/bash
set -e
# This script installs the build dependencies for CI builds.

# Prepare OPAM configuration
export OPAMROOT="$(pwd)/opamroot"
export OPAMJOBS="$((2*$CPU_CORES))"
export OPAM_EDITOR="$(which false)"

# Make sure we got a good OPAM
test -d "$OPAMROOT" || (mkdir "$OPAMROOT" && opam init --no-setup -y)
eval `opam conf env`
if test $(find "$OPAMROOT/repo/package-index" -mtime +0); then
    # last update was more than a day ago
    opam update
else
    echo "[opam-ci] Not updating opam."
fi
test -d "$OPAMROOT/repo/coq-extra-dev" || opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev -p 5
test -d "$OPAMROOT/repo/coq-core-dev" || opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev -p 5
test -d "$OPAMROOT/repo/coq-released" || opam repo add coq-released https://coq.inria.fr/opam/released -p 10

# Install fixed versions of some dependencies
echo
while (( "$#" )); do # while there are arguments left
    PACKAGE="$1" ; shift
    VERSION="$1" ; shift
    # Check if the pin is already set
    if opam pin list | fgrep "$PACKAGE.$VERSION " > /dev/null; then
        echo "[opam-ci] $PACKAGE already pinned to $VERSION"
    else
        echo "[opam-ci] Pinning $PACKAGE to $VERSION"
        opam pin add "$PACKAGE" "$VERSION" -k version -y
    fi
done

# Install build-dependencies
echo
make build-dep Y=1

# done
echo
coqc -v
