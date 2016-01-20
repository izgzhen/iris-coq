# Copyright (c) 2012-2015, Robbert Krebbers.
# This file is distributed under the terms of the BSD license.
import os, glob, string

modules = ["prelude", "modures", "iris", "barrier"]
Rs = '-Q . ""'
env = DefaultEnvironment(ENV = os.environ,tools=['default', 'Coq'], COQFLAGS=Rs)

# Coq dependencies
vs = [x for m in modules for x in glob.glob(m + '/*.v')]
if os.system('coqdep ' + Rs + ' ' + ' '.join(map(str, vs)) + ' > deps'): Exit(2)
ParseDepends('deps')

# Coq files
for v in vs: env.Coq(v)
