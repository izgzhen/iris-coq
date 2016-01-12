# Copyright (c) 2012-2015, Robbert Krebbers.
# This file is distributed under the terms of the BSD license.
import SCons.Defaults, SCons.Tool, SCons.Util, os

def coq_emitter(target, source, env):
  base, _ = os.path.splitext(str(target[0]))
  target.append(base + ".glob")
  return target, source
Coq = SCons.Builder.Builder(
  action = '$COQC $COQFLAGS -q $SOURCE',
  suffix = '.vo',
  src_suffix = '.v',
  emitter = coq_emitter
)

def generate(env):
  env['COQC'] = 'coqc'
  env.Append(BUILDERS = { 'Coq' : Coq })

def exists(env):
  return env.Detect('coqc')
