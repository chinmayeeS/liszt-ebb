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

local function is_num(obj) return type(obj) == 'number' end
local function is_bool(obj) return type(obj) == 'boolean' end

-------------------------------------------------------------------------------

local Grid2d = {}
local Grid3d = {}
Grid2d.__index = Grid2d
Grid3d.__index = Grid3d

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--                                  2d Grid
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

local function rectangles_2d(X, Y, xb, yb)
  return {
    boundary_xneg = { {0,xb-1},    {0,Y-1}     },
    boundary_xpos = { {X-xb,X-1},  {0,Y-1}     },
    boundary_yneg = { {xb,X-xb-1}, {0,yb-1}    },
    boundary_ypos = { {xb,X-xb-1}, {Y-yb,Y-1}  },
    interior      = { {xb,X-xb-1}, {yb,Y-yb-1} },
  }
end

local function setup2dCells(grid)
  local Cx, Cy  = grid:xSize(), grid:ySize()
  local xw, yw  = grid:xCellWidth(), grid:yCellWidth()
  local xo, yo  = grid:xOrigin(), grid:yOrigin()
  local xn_bd   = grid:xBoundaryDepth()
  local yn_bd   = grid:yBoundaryDepth()
  local cells   = grid.cells

  -- offset
  cells:NewFieldMacro('__apply_macro', L.Macro(function(c,x,y)
    return ebb `L.Affine(cells, {{1,0,x},
                                 {0,1,y}}, c)                   end))

  -- Boundary/Interior subsets
  cells:NewDivision(rectangles_2d(Cx, Cy, xn_bd, yn_bd))

  cells:NewFieldReadFunction('center', ebb(c)
    return L.vec2d({ xo + xw * (L.double(L.xid(c)) + 0.5),
                     yo + yw * (L.double(L.yid(c)) + 0.5) })  end)

  local xsnap = grid:xUsePeriodic() and wrap_idx or clamp_idx
  local ysnap = grid:yUsePeriodic() and wrap_idx or clamp_idx
  rawset(cells, 'locate', L.Macro(function(pos)
    return ebb `L.UNSAFE_ROW({xsnap((pos[0] - xo)/xw, Cx),
                              ysnap((pos[1] - yo)/yw, Cy)}, cells)
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

  cells:NewFieldReadFunction('in_boundary', ebb(c)
    return c.xneg_depth > 0 or c.xpos_depth > 0 or
           c.yneg_depth > 0 or c.ypos_depth > 0           end)
  cells:NewFieldMacro('in_interior', L.Macro(function(c)
    return ebb ` not c.in_boundary                              end))
end

-------------------------------------------------------------------------------

function Grid.NewGrid2d(params)
  local calling_convention = [[
NewGrid2d should be called with named parameters:
Grid.NewGrid2d{
  name           = string,  -- name of grid relation
  size           = {#,#},   -- number of cells in x,y (including boundary)
  origin         = {#,#},   -- x,y coordinates of grid origin
  width          = {#,#},   -- x,y width of grid in coordinate system
  [boundary_depth = {#,#},] -- depth of boundary region (default: {1,1})
                            -- must be 0 on directions that are periodic
  [periodic_boundary = {bool,bool},] -- use periodic boundary conditions
                                     -- (default: {false,false})
}]]
  local function check_params(params)
    if type(params) ~= 'table' then return false end
    if type(params.name) ~= 'string' or
       type(params.size) ~= 'table' or
       type(params.origin) ~= 'table' or
       type(params.width) ~= 'table' then return false end
    local check = is_num(params.size[1])    and is_num(params.size[2]) and
                  is_num(params.origin[1])  and is_num(params.origin[2]) and
                  is_num(params.width[1])   and is_num(params.width[2])
    local bd = params.boundary_depth
    local pb = params.periodic_boundary
    if bd then check = check and type(bd) == 'table' and
                                 is_num(bd[1]) and is_num(bd[2]) end
    if pb then check = check and type(pb) == 'table' and
                                 is_bool(pb[1]) and is_bool(pb[2]) end
    if bd and pb then check = check and not (pb[1] and bd[1] ~= 0) and
                                        not (pb[2] and bd[2] ~= 0) end
    return check
  end
  if not check_params(params) then error(calling_convention, 2) end

  -- default parameters
  local pb      = params.periodic_boundary or {false, false}
  local bd      = params.boundary_depth    or {1, 1}

  local grid = setmetatable({
    _n_xy       = copy_table(params.size),
    _origin     = copy_table(params.origin),
    _dims       = copy_table(params.width),
    _bd_depth   = bd,
    _periodic   = pb,
    -- relations
    cells       = L.NewRelation { name     = params.name..'_cells',
                                  dims     = params.size,
                                  periodic = pb },
  }, Grid2d)

  setup2dCells(grid)

  return grid
end

function Grid2d:xSize()             return self._n_xy[1]            end
function Grid2d:ySize()             return self._n_xy[2]            end
function Grid2d:xOrigin()           return self._origin[1]          end
function Grid2d:yOrigin()           return self._origin[2]          end
function Grid2d:xWidth()            return self._dims[1]            end
function Grid2d:yWidth()            return self._dims[2]            end
function Grid2d:xBoundaryDepth()    return self._bd_depth[1]        end
function Grid2d:yBoundaryDepth()    return self._bd_depth[2]        end
function Grid2d:xUsePeriodic()      return self._periodic[1]        end
function Grid2d:yUsePeriodic()      return self._periodic[2]        end
function Grid2d:xCellWidth()  return self:xWidth() / (1.0 * self:xSize()) end
function Grid2d:yCellWidth()  return self:yWidth() / (1.0 * self:ySize()) end

function Grid2d:Size()            return copy_table(self._n_xy)     end
function Grid2d:Origin()          return copy_table(self._origin)   end
function Grid2d:Width()           return copy_table(self._dims)     end
function Grid2d:BoundaryDepth()   return copy_table(self._bd_depth) end
function Grid2d:UsePeriodic()     return copy_table(self._periodic) end
function Grid2d:CellWidth()
  return { self:xCellWidth(), self:yCellWidth() }
end

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--                                  3d Grid
-------------------------------------------------------------------------------
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

local function setup3dCells(grid)
  local Cx, Cy, Cz  = grid:xSize(), grid:ySize(), grid:zSize()
  local xw, yw, zw  = grid:xCellWidth(), grid:yCellWidth(), grid:zCellWidth()
  local xo, yo, zo  = grid:xOrigin(), grid:yOrigin(), grid:zOrigin()
  local xn_bd       = grid:xBoundaryDepth()
  local yn_bd       = grid:yBoundaryDepth()
  local zn_bd       = grid:zBoundaryDepth()
  local cells       = grid.cells

  -- relative offset
  cells:NewFieldMacro('__apply_macro', L.Macro(function(c,x,y,z)
      return ebb `L.Affine(cells, {{1,0,0,x},
                                   {0,1,0,y},
                                   {0,0,1,z}}, c)               end))

  -- Boundary/Interior subsets
  cells:NewDivision(rectangles_3d(Cx, Cy, Cz, xn_bd, yn_bd, zn_bd))

  cells:NewFieldReadFunction('center', ebb(c)
    return L.vec3d({ xo + xw * (L.double(L.xid(c)) + 0.5),
                     yo + yw * (L.double(L.yid(c)) + 0.5),
                     zo + zw * (L.double(L.zid(c)) + 0.5) })  end)

  local xsnap = grid:xUsePeriodic() and wrap_idx or clamp_idx
  local ysnap = grid:yUsePeriodic() and wrap_idx or clamp_idx
  local zsnap = grid:zUsePeriodic() and wrap_idx or clamp_idx
  rawset(cells, 'locate', L.Macro(function(pos)
    return ebb `L.UNSAFE_ROW({xsnap((pos[0] - xo) / xw, Cx),
                              ysnap((pos[1] - yo) / yw, Cy),
                              zsnap((pos[2] - zo) / zw, Cz)}, cells)
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

-------------------------------------------------------------------------------

function Grid.NewGrid3d(params)
  local calling_convention = [[
NewGrid3d should be called with named parameters:
Grid.NewGrid3d{
  name           = string,  -- name of grid relation
  size           = {#,#,#}, -- number of cells in x,y,z (including boundary)
  origin         = {#,#,#}, -- x,y,z coordinates of grid origin
  width          = {#,#,#}, -- x,y,z width of grid in coordinate system
  [boundary_depth = {#,#,#},] -- depth of boundary region (default: {1,1,1})
                              -- must be 0 on directions that are periodic
  [periodic_boundary = {bool,bool,bool},] -- use periodic boundary conditions
                                          -- (default: {false,false,false})
}]]
  local function check_params(params)
    if type(params) ~= 'table' then return false end
    if type(params.name) ~= 'string' or
       type(params.size) ~= 'table' or
       type(params.origin) ~= 'table' or
       type(params.width) ~= 'table' then return false end
    local check = true
    for i=1,3 do
      check = check and is_num(params.size[i])
                    and is_num(params.origin[i])
                    and is_num(params.width[i])
    end
    local bd = params.boundary_depth
    local pb = params.periodic_boundary
    if bd then check = check and type(bd) == 'table' and is_num(bd[1]) and
                                       is_num(bd[2]) and is_num(bd[3]) end
    if pb then check = check and type(pb) == 'table' and is_bool(pb[1]) and
                                      is_bool(pb[2]) and is_bool(pb[3]) end
    if bd and pb then check = check and not (pb[1] and bd[1] ~= 0) and
                                        not (pb[2] and bd[2] ~= 0) and
                                        not (pb[3] and bd[3] ~= 0) end
    return check
  end
  if not check_params(params) then error(calling_convention, 2) end

  -- default
  local wrap_bnd      = params.periodic_boundary or {false, false, false}
  local bnd_depth     = params.boundary_depth    or {1, 1, 1}

  local grid = setmetatable({
    _n_xyz      = copy_table(params.size),
    _origin     = copy_table(params.origin),
    _dims       = copy_table(params.width),
    _bd_depth   = bnd_depth,
    _periodic   = wrap_bnd,
    -- relations
    cells       = L.NewRelation { name     = params.name..'_cells',
                                  dims     = params.size,
                                  periodic = wrap_bnd },
  }, Grid3d)

  setup3dCells(grid)

  return grid
end

function Grid3d:xSize()             return self._n_xyz[1]           end
function Grid3d:ySize()             return self._n_xyz[2]           end
function Grid3d:zSize()             return self._n_xyz[3]           end
function Grid3d:xOrigin()           return self._origin[1]          end
function Grid3d:yOrigin()           return self._origin[2]          end
function Grid3d:zOrigin()           return self._origin[3]          end
function Grid3d:xWidth()            return self._dims[1]            end
function Grid3d:yWidth()            return self._dims[2]            end
function Grid3d:zWidth()            return self._dims[3]            end
function Grid3d:xBoundaryDepth()    return self._bd_depth[1]        end
function Grid3d:yBoundaryDepth()    return self._bd_depth[2]        end
function Grid3d:zBoundaryDepth()    return self._bd_depth[3]        end
function Grid3d:xUsePeriodic()      return self._periodic[1]        end
function Grid3d:yUsePeriodic()      return self._periodic[2]        end
function Grid3d:zUsePeriodic()      return self._periodic[3]        end
function Grid3d:xCellWidth()  return self:xWidth() / (1.0 * self:xSize()) end
function Grid3d:yCellWidth()  return self:yWidth() / (1.0 * self:ySize()) end
function Grid3d:zCellWidth()  return self:zWidth() / (1.0 * self:zSize()) end

function Grid3d:Size()            return copy_table(self._n_xyz)    end
function Grid3d:Origin()          return copy_table(self._origin)   end
function Grid3d:Width()           return copy_table(self._dims)     end
function Grid3d:BoundaryDepth()   return copy_table(self._bd_depth) end
function Grid3d:UsePeriodic()     return copy_table(self._periodic) end
function Grid3d:CellWidth()
  return { self:xCellWidth(), self:yCellWidth(), self:zCellWidth() }
end
