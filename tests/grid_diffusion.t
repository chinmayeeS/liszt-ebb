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
local L = require 'ebblib'
local Grid  = require 'ebb.domains.grid' 

local N = 1024

-- new relation
local grid = Grid.NewGrid2d{
              size           = {16,8},
              origin         = {0,0},
              width          = {1.0,1.0},
              boundary_depth = {2, 0},
              periodic_boundary = {true, false},
              partitions        = {2, 1}
            }

local cells = grid.cells

-- new fields on relations
cells:NewField('f', L.double)
cells:NewField('f_new', L.double)
cells:NewField('v', L.vec3d):Load({0.1, 0.7, 1.5})

-- load fields
cells.f:Load(0)
cells.f_new:Load(0.5)

local g_float = L.Global(L.float, 0)
local g_vec3d = L.Global(L.vec3i, {0.1, 0.3, 0.9})


-- ebb kernels

local ebb init_checker( c : cells )
  var color = (L.xid(c) + L.yid(c)) % 2
  if color == 0 then c.f = 2.0
                else c.f = 1.0 end
end

local ebb diffuse( c : cells )
  var avg = 0.25 * ( c(1,0).f + c(-1,0).f + c(0,1).f + c(0,-1).f )
  c.f_new = c.f + 0.25 * (avg - c.f)
  g_float += 1
end

local ebb check_vals( c : cells )
  var color = (L.xid(c) + L.yid(c)) % 2
  var goal  = 1.75
  if color == 1 then goal = 1.25 end
  L.assert(c.f_new == goal)
end

cells:foreach(init_checker)

for i = 1,3 do
  cells:foreach(diffuse)
  g_float:set(0)
  cells:foreach(check_vals)
end

-- print all API calls
local A = require 'ebb.src.api_log'
A.log:print()
