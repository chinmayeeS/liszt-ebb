#!/usr/bin/env python

# NOTE: Run Admiral in code-emission mode, set '-fdebug 1', and feed the stdout
# (not stderr) output into this script. Make sure you compile the resulting
# Regent code with the same value for -fparallelize-dop as the original Liszt.

import fileinput
import re

# Add required imports
print 'import "regent"'
print 'local HDF5 = terralib.includec("hdf5/serial/hdf5.h")'
print 'local C = terralib.includecstring[['
print '#include <math.h>'
print '#include <stdlib.h>'
print '#include <stdio.h>'
print '#include <string.h>'
print ']]'

for line in fileinput.input():
    line = line[:-1]
    # Remove type annotations where they can be inferred
    line = re.sub(r'for ([\w$#]+) : .* in ', r'for \1 in ', line)
    line = re.sub(r'var ([\w$#]+) : [^:=]* =', r'var \1 =', line)
    # Make variable names valid identifiers
    line = re.sub(r'\$\w+#([0-9]+)', r'v\1', line)
    line = re.sub(r'\$(\w+)\$([0-9]+)', r'v\1__\2', line)
    line = re.sub(r'\$(\w+)', r'v\1', line)
    # Remove remaining debug numbers
    line = re.sub(r'region#[0-9]+', r'region', line)
    line = re.sub(r'ispace#[0-9]+', r'ispace', line)
    # Wrap type casts
    line = re.sub(r'(float\[[0-9]+\])\(', r'[\1](', line)
    line = re.sub(r'(double\[[0-9]+\])\(', r'[\1](', line)
    line = re.sub(r'(&\w+)\(', r'[\1](', line)
    # inf -> math.huge
    line = re.sub(r'([^\w])inf', r'\1math.huge', line)
    # Add proper namespaces to function calls
    line = re.sub(r'([^\w])(printf|snprintf|malloc|free|memcpy)\(', r'\1C.\2(', line)
    line = re.sub(r'([^\w])(acos|asin|atan|cbrt|tan|pow|fmod)\(', r'\1C.\2(', line)
    line = line.replace('H5', 'HDF5.H5')
    line = line.replace('legion_', 'regentlib.c.legion_')
    line = line.replace('std.', 'regentlib.')
    # Remove unparsable terra annotations
    line = re.sub(r'extern global (.*) : \w+', r'\1', line)
    # (@x). -> x.
    line = re.sub(r'\(@(\w+)\)\.', r'\1.', line)
    # Print filtered line
    print line

# Add final compile command
print 'regentlib.saveobj(main, "a.out", "executable", nil, {"-lm","-lhdf5_serial"})'
