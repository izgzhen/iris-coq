#!/bin/bash
set -e
## This script installs the build dependencies for CI builds.
function run_and_print() {
    echo "$ $@"
    "$@"
}

# Prepare OPAM configuration
export OPAMROOT="$(pwd)/opamroot"
export OPAMJOBS="$((2*$CPU_CORES))"
export OPAM_EDITOR="$(which false)"

# Make sure we got a good OPAM.
test -d "$OPAMROOT" || (mkdir "$OPAMROOT" && run_and_print opam init --no-setup -y)
eval `opam conf env`
# Delete old pins from opam.pins times.
run_and_print opam pin remove coq-stdpp -n
run_and_print opam pin remove coq-iris -n
# Make sure the pin for the builddep package is not stale.
run_and_print make build-dep/opam

# Get us all the latest repositories
if test $(find "$OPAMROOT/repo/package-index" -mtime +0); then
    # last update was more than a day ago
    run_and_print opam update
else
    # only update iris-dev
    if test -d "$OPAMROOT/repo/iris-dev"; then run_and_print opam update iris-dev; fi
fi
test -d "$OPAMROOT/repo/coq-extra-dev" && run_and_print opam repo remove coq-extra-dev
test -d "$OPAMROOT/repo/coq-core-dev" || run_and_print opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev -p 5
test -d "$OPAMROOT/repo/coq-released" || run_and_print opam repo add coq-released https://coq.inria.fr/opam/released -p 10
test -d "$OPAMROOT/repo/iris-dev" || run_and_print opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git -p 20
echo

# We really want to run all of the following in one opam transaction, but due to opam limitations,
# that is not currently possible.

# Install fixed versions of some dependencies.
echo
while (( "$#" )); do # while there are arguments left
    PACKAGE="$1" ; shift
    VERSION="$1" ; shift

    # Check if the pin is already set
    if opam pin list | fgrep "$PACKAGE.$VERSION " > /dev/null; then
        echo "[opam-ci] $PACKAGE already pinned to $VERSION"
    else
        echo "[opam-ci] Pinning $PACKAGE to $VERSION"
        run_and_print opam pin add "$PACKAGE" "$VERSION" -k version -y
    fi
done

# Upgrade cached things.
echo
echo "[opam-ci] Upgrading opam"
run_and_print opam upgrade -y

# Install build-dependencies.
echo
echo "[opam-ci] Installing build-dependencies"
make build-dep OPAMFLAGS=-y

# done
echo
coqc -v
