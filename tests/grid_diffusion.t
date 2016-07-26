-- The MIT License (MIT)
--
-- Copyright (c) 2015 Stanford University.
-- All rights reserved.
--
-- Permission is hereby granted, free of charge, to any person obtaining a
-- copy of this software and associated documentation files (the "Software"),
-- to deal in the Software without restriction, including without limitation
-- the rights to use, copy, modify, merge, publish, distribute, sublicense,
-- and/or sell copies of the Software, and to permit persons to whom the
-- Software is furnished to do so, subject to the following conditions:
--
-- The above copyright notice and this permission notice shall be included
-- in all copies or substantial portions of the Software.
--
-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
-- IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
-- FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
-- AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
-- LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
-- FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
-- DEALINGS IN THE SOFTWARE.

import 'ebb'

local A    = require 'admiral'
local GRID = require 'ebb.domains.grid'
local L    = require 'ebblib'

-------------------------------------------------------------------------------

local grid = GRID.NewGrid2d{
               size              = {16,8},
               origin            = {0,0},
               width             = {1.0,1.0},
               boundary_depth    = {2, 0},
               periodic_boundary = {false, true},
             }

grid.cells:NewField('f', L.double):Load(0)
grid.cells:NewField('f_new', L.double):Load(0.5)
grid.cells:NewField('v', L.vec3d):Load({0.1, 0.7, 1.5})

local timestep    = L.Constant(L.double, 0.45)
local conduction  = L.Constant(L.double, 1.0)

local max_diff = L.Global(L.double, 0.0)
local g_float  = L.Global(L.float, 0)
local g_vec3d  = L.Global(L.vec3d, {0.1, 0.3, 0.9})

-------------------------------------------------------------------------------

local ebb init_checker( c : grid.cells )
  var color = (L.xid(c) + L.yid(c)) % 2
  if color == 0 then c.f = 2.0
                else c.f = 1.0 end
end

local ebb diffuse( c : grid.cells )
  var avg = 0.25 * ( c(1,0).f + c(-1,0).f + c(0,1).f + c(0,-1).f )
  var diff = avg - c.f
  c.f_new = c.f + timestep * conduction * diff
  g_float += 1
end

local ebb measure_max_diff ( c : grid.cells )
  var avg  = 0.25 * ( c(1,0).f + c(-1,0).f + c(0,1).f + c(0,-1).f )
  var diff = avg - c.f
  max_diff max= L.fabs(diff)
end

local ebb check_vals( c : grid.cells )
  var color = (L.xid(c) + L.yid(c)) % 2
  var goal  = 1.75
  if color == 1 then goal = 1.25 end
  L.assert(goal == goal)
end

-------------------------------------------------------------------------------

grid.cells:foreach(init_checker)

for i = 1,3 do
  grid.cells:foreach(diffuse)
  g_float:set(0)
  grid.cells:foreach(check_vals)
end

-------------------------------------------------------------------------------

A.translateAndRun()
