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

import "ebb"

local L = require 'ebblib'
local R = require 'ebb.src.relations'

local Grid = {}
package.loaded["ebb.domains.grid"] = Grid

-------------------------------------------------------------------------------

local int_floor = L.Macro(function(v)
  return ebb `L.int(L.floor(v))
end)
local max_impl = L.Macro(function(a,b)
  return ebb `L.imax(a, b)
end)
local min_impl = L.Macro(function(a,b)
  return ebb `L.imin(a, b)
end)
local clamp_impl = L.Macro(function(x, lower, upper)
  return ebb `max_impl(lower, min_impl(upper, x))
end)
-- convert a potentially continuous signed value x to
-- an address modulo the given uint m
local wrap_idx = L.Macro(function(x, m)
  return ebb `L.uint64(L.fmod(x,m) + m) % m
end)
local clamp_idx = L.Macro(function(x, limit)
  return ebb `L.uint64(clamp_impl(x, 0.0, L.double(limit-1)))
end)

local function copy_table(tbl)
  local cpy = {}
  for k,v in pairs(tbl) do cpy[k] = v end
  return cpy
end

-------------------------------------------------------------------------------

local function rectangles_3d(X, Y, Z, xb, yb, zb)
  return {
    boundary_xneg = { {0,xb-1},    {0,Y-1},     {0,Z-1}     },
    boundary_xpos = { {X-xb,X-1},  {0,Y-1},     {0,Z-1}     },
    boundary_yneg = { {xb,X-xb-1}, {0,yb-1},    {0,Z-1}     },
    boundary_ypos = { {xb,X-xb-1}, {Y-yb,Y-1},  {0,Z-1}     },
    boundary_zneg = { {xb,X-xb-1}, {yb,Y-yb-1}, {0,zb-1}    },
    boundary_zpos = { {xb,X-xb-1}, {yb,Y-yb-1}, {Z-zb,Z-1}  },
    interior      = { {xb,X-xb-1}, {yb,Y-yb-1}, {zb,Z-zb-1} },
  }
end

local function addHelpers(cells)
  local Cx, Cy, Cz  = cells._dims[1], cells._dims[2], cells._dims[3]
  local xw, yw, zw  = cells._width[1], cells._width[2], cells._width[3]
  local xo, yo, zo  = cells._origin[1], cells._origin[2], cells._origin[3]
  local xn_bd       = cells._boundary_depth[1]
  local yn_bd       = cells._boundary_depth[2]
  local zn_bd       = cells._boundary_depth[3]

  -- relative offset
  cells:NewFieldMacro('__apply_macro', L.Macro(function(c,x,y,z)
      return ebb `L.Affine(cells, {{1,0,0,x},
                                   {0,1,0,y},
                                   {0,0,1,z}}, c)
  end))

  -- Boundary/Interior subsets
  cells:NewDivision(rectangles_3d(Cx, Cy, Cz, xn_bd, yn_bd, zn_bd))

  cells:NewFieldReadFunction('center', ebb(c)
    return L.vec3d({ xo + xw / Cx * (L.double(L.xid(c)) + 0.5),
                     yo + yw / Cy * (L.double(L.yid(c)) + 0.5),
                     zo + zw / Cz * (L.double(L.zid(c)) + 0.5) })
  end)

  local xsnap = cells._periodic[1] and wrap_idx or clamp_idx
  local ysnap = cells._periodic[2] and wrap_idx or clamp_idx
  local zsnap = cells._periodic[3] and wrap_idx or clamp_idx
  rawset(cells, 'locate', L.Macro(function(pos)
    return ebb `L.UNSAFE_ROW({xsnap((pos[0] - xo) / xw * Cx, Cx),
                              ysnap((pos[1] - yo) / yw * Cy, Cy),
                              zsnap((pos[2] - zo) / zw * Cz, Cz)}, cells)
  end))

  -- boundary depths
  cells:NewFieldMacro('xneg_depth', L.Macro(function(c)
    return ebb `max_impl(L.int(xn_bd - L.xid(c)), 0)            end))
  cells:NewFieldMacro('xpos_depth', L.Macro(function(c)
    return ebb `max_impl(L.int(L.xid(c) - (Cx-1 - xn_bd)), 0)   end))
  cells:NewFieldMacro('yneg_depth', L.Macro(function(c)
    return ebb `max_impl(L.int(yn_bd - L.yid(c)), 0)            end))
  cells:NewFieldMacro('ypos_depth', L.Macro(function(c)
    return ebb `max_impl(L.int(L.yid(c) - (Cy-1 - yn_bd)), 0)   end))
  cells:NewFieldMacro('zneg_depth', L.Macro(function(c)
    return ebb `max_impl(L.int(zn_bd - L.zid(c)), 0)            end))
  cells:NewFieldMacro('zpos_depth', L.Macro(function(c)
    return ebb `max_impl(L.int(L.zid(c) - (Cz-1 - zn_bd)), 0)   end))

  cells:NewFieldReadFunction('in_boundary', ebb(c)
    return c.xneg_depth > 0 or c.xpos_depth > 0 or
           c.yneg_depth > 0 or c.ypos_depth > 0 or
           c.zneg_depth > 0 or c.zpos_depth > 0
  end)
  cells:NewFieldMacro('in_interior', L.Macro(function(c)
    return ebb ` not c.in_boundary
  end))
end

function Grid.NewGrid(params)
  local params = copy_table(params)
  params.mode = 'GRID'
  local grid = L.NewRelation(params)
  addHelpers(grid)
  return grid
end
