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

local R = {}
package.loaded["ebb.src.relations"] = R

local Pre   = require "ebb.src.prelude"
local T     = require "ebb.src.types"
local F     = require "ebb.src.functions"
local M     = require "ebb.src.main"
local UTIL  = require "ebb.src.util"

local all        = UTIL.all
local copy_table = UTIL.copy_table

-------------------------------------------------------------------------------

local valid_name_err_msg_base =
  "must be valid Lua Identifiers: a letter or underscore,"..
  " followed by zero or more underscores, letters, and/or numbers"
local valid_name_err_msg = {
  relation = "Relation names "  .. valid_name_err_msg_base,
  field    = "Field names "     .. valid_name_err_msg_base,
  subset   = "Subset names "    .. valid_name_err_msg_base
}
local function is_valid_lua_identifier(name)
  if type(name) ~= 'string' then return false end
  -- regex for valid LUA identifiers
  if not name:match('^[_%a][_%w]*$') then return false end
  return true
end

local function is_num(x) return type(x) == 'number' end
local function is_bool(x) return type(x) == 'boolean' end
local function is_int(x) return type(x) == 'number' and x == math.floor(x) end

-------------------------------------------------------------------------------

local Relation    = {}
Relation.__index  = Relation
R.Relation        = Relation
local function is_relation(obj) return getmetatable(obj) == Relation end
R.is_relation     = is_relation


local Field       = {}
Field.__index     = Field
R.Field           = Field
local function is_field(obj) return getmetatable(obj) == Field end
R.is_field        = is_field

local Subset      = {}
Subset.__index    = Subset
R.Subset          = Subset
local function is_subset(obj) return getmetatable(obj) == Subset end
R.is_subset       = is_subset

-------------------------------------------------------------------------------
--[[  Relation methods                                                     ]]--
-------------------------------------------------------------------------------

-- A Relation must be in one of the following MODES:
--    PLAIN
--    GRID
--    COUPLED
function Relation:isPlain()       return self._mode == 'PLAIN'      end
function Relation:isGrid()        return self._mode == 'GRID'       end
function Relation:isCoupled()     return self._mode == 'COUPLED'    end

local errorMsg = [[NewRelation must be called as follows:
local myrel = L.NewRelation {
  name = string,
  mode = 'PLAIN' | 'GRID' | 'COUPLED',
  --------------------------------------------------------------------------
  -- if mode == 'PLAIN':
  --------------------------------------------------------------------------
  size = 35,
  --------------------------------------------------------------------------
  -- if mode == 'GRID':
  --------------------------------------------------------------------------
  dims = {#,#,#}, -- number of cells in x,y,z (incl. boundary)
  origin = {#,#,#}, -- coordinates of grid origin (incl. boundary)
  width = {#,#,#}, -- x,y,z width of grid (incl. boundary)
  [boundary_depth = {#,#,#},] -- depth of boundary region (default: {1,1,1})
                              -- must be 0 on directions that are periodic
  [periodic = {bool,bool,bool},] -- use periodic boundary conditions
                                 -- (default: {false,false,false})
  --------------------------------------------------------------------------
  -- if mode == 'COUPLED':
  --------------------------------------------------------------------------
  size = 100,
  coupled_with = other_relation,
  coupling_field = 'fld_name',
  max_skew = 3.0,
  max_xfer_num = 10,
  xfer_stencil = {{0,0,1},{0,0,-1},...},
}]]

local relation_uid = 0
function R.NewRelation(params)
  -- Check the parameters
  local function checkParams(params)
    local check =
      type(params) == 'table' and
      is_valid_lua_identifier(params.name) and
      (params.mode == 'PLAIN' or
       params.mode == 'GRID' or
       params.mode == 'COUPLED')
    if params.mode == 'PLAIN' then
      check = check and
        is_int(params.size)
    elseif params.mode == 'GRID' then
      check = check and
        terralib.israwlist(params.dims) and
        #params.dims == 3 and all(params.dims, is_int) and
        terralib.israwlist(params.origin) and
        #params.origin == 3 and all(params.origin, is_num) and
        terralib.israwlist(params.width) and
        #params.width == 3 and all(params.width, is_num)
      local bd = params.boundary_depth
      local pb = params.periodic_boundary
      if bd then
        check = check and
          terralib.israwlist(bd) and #bd == 3 and all(bd, is_num)
      end
      if pb then
        check = check and
          terralib.israwlist(pb) and #pb == 3 and all(pb, is_bool)
      end
      if bd and pb then
        check = check and
          not (pb[1] and bd[1] ~= 0) and
          not (pb[2] and bd[2] ~= 0) and
          not (pb[3] and bd[3] ~= 0)
      end
    elseif params.mode == 'COUPLED' then
      check = check and
        is_int(params.size) and
        is_relation(params.coupled_with) and
        is_valid_lua_identifier(params.coupling_field) and
        is_num(params.max_skew) and
        is_int(params.max_xfer_num) and
        terralib.israwlist(params.xfer_stencil) and
        all(params.xfer_stencil, function(dir) return
          terralib.israwlist(dir) and #dir == 3 and all(dir, is_int)
        end)
    else assert(false) end
    return check
  end
  if not checkParams(params) then error(errorMsg, 2) end

  -- construct the relation
  local rel = setmetatable( {
    _name       = params.name,
    _mode       = params.mode,
    _uid        = relation_uid,
    _fields     = terralib.newlist(),
    _divisions  = terralib.newlist(),
    _macros     = terralib.newlist(),
    _functions  = terralib.newlist(),
  }, Relation)
  relation_uid = relation_uid + 1 -- increment unique id counter

  -- perform mode-dependent setup
  local size
  if params.mode == 'PLAIN' then
    -- size calculation
    size = params.size
  elseif params.mode == 'GRID' then
    -- size calculation
    size = params.dims[1] * params.dims[2] * params.dims[3]
    -- defaults
    local bd_depth = params.boundary_depth or {1, 1, 1}
    local periodic = params.periodic       or {false, false, false}
    -- mode-dependent values
    rawset(rel, '_dims',              copy_table(params.dims))
    rawset(rel, '_origin',            copy_table(params.origin))
    rawset(rel, '_width',             copy_table(params.width))
    rawset(rel, '_boundary_depth',    copy_table(bd_depth))
    rawset(rel, '_periodic',          copy_table(periodic))
    rawset(rel, '_coarsening_fields', terralib.newlist())
  elseif params.mode == 'COUPLED' then
    -- size calculation
    size = params.size
    -- mode-dependent values
    rawset(rel, '_coupling_field',
           rel:NewField(params.coupling_field, params.coupled_with))
    rawset(rel, '_max_skew', params.max_skew)
    rawset(rel, '_max_xfer_num', params.max_xfer_num)
    rawset(rel, '_xfer_stencil', terralib.newlist(params.xfer_stencil))
  else assert(false) end
  rawset(rel, '_size',  size)

  -- register & return the relation
  M.decls():insert(M.AST.NewRelation(rel))
  return rel
end

function Relation:_INTERNAL_UID()
  return self._uid
end

function Relation:Name()
  return self._name
end

function Relation:Mode()
  return self._mode
end

function Relation:Size()
  return self._size
end

function Relation:Dims()
  if not self:isGrid() then
    return { self:Size() }
  end
  return copy_table(self._dims)
end

function Relation:Fields()
  return self._fields
end

function Relation:Divisions()
  return self._divisions
end

function Relation:foreach(user_func, ...)
  if not F.is_function(user_func) then
    error('foreach(): expects an ebb function as the first argument', 2)
  end
  user_func:_doForEach(self, ...)
end

-- prevent user from modifying the lua table
function Relation:__newindex(fieldname,value)
  error("Cannot assign members to Relation object "..
      "(did you mean to call relation:New...?)", 2)
end

-------------------------------------------------------------------------------
--[[  Grids                                                                ]]--
-------------------------------------------------------------------------------

function R.Relation:Origin()
  assert(self:isGrid())
  return copy_table(self._origin)
end

function R.Relation:Width()
  assert(self:isGrid())
  return copy_table(self._width)
end

function R.Relation:BoundaryDepth()
  assert(self:isGrid())
  return copy_table(self._boundary_depth)
end

function R.Relation:Periodic()
  assert(self:isGrid())
  return copy_table(self._periodic)
end

function R.Relation:CellWidth()
  assert(self:isGrid())
  return { self._width[1] / (1.0 * self._dims[1]),
           self._width[2] / (1.0 * self._dims[2]),
           self._width[3] / (1.0 * self._dims[3]) }
end

function R.Relation:CoarseningFields()
  assert(self:isGrid())
  return self._coarsening_fields:copy()
end

-------------------------------------------------------------------------------
--[[  Coupled relations                                                    ]]--
-------------------------------------------------------------------------------

function Relation:CouplingField()
  assert(self:isCoupled())
  return self._coupling_field
end

function Relation:MaxSkew()
  assert(self:isCoupled())
  return self._max_skew
end

function Relation:MaxXferNum()
  assert(self:isCoupled())
  return self._max_xfer_num
end

function Relation:XferStencil()
  assert(self:isCoupled())
  return self._xfer_stencil
end

-------------------------------------------------------------------------------
--[[  Virtual fields                                                       ]]--
-------------------------------------------------------------------------------

function Relation:NewFieldMacro(name, macro)
  if not name or type(name) ~= "string" then
    error("NewFieldMacro() expects a string as the first argument", 2)
  end
  if not is_valid_lua_identifier(name) then
    error(valid_name_err_msg.field, 2)
  end
  if self[name] then
    error("Cannot create a new field-macro with name '"..name.."'  "..
          "That name is already being used.", 2)
  end

  if not Pre.is_macro(macro) then
    error("NewFieldMacro() expects a Macro as the 2nd argument", 2)
  end

  rawset(self, name, macro)
  self._macros:insert(macro)
  return macro
end

local FieldDispatcher     = {}
FieldDispatcher.__index   = FieldDispatcher
R.FieldDispatcher         = FieldDispatcher
local function NewFieldDispatcher()
  return setmetatable({
    _reader   = nil,
    _writer   = nil,
    _reducers = {},
  }, FieldDispatcher)
end
local function isfielddispatcher(obj)
  return getmetatable(obj) == FieldDispatcher
end
R.isfielddispatcher = isfielddispatcher

local function getFieldDispatcher(rel, fname, ufunc)
  if not fname or type(fname) ~= "string" then
    error("NewField*Function() expects a string as the first argument", 3)
  end
  if not is_valid_lua_identifier(fname) then
    error(valid_name_err_msg.field, 3)
  end
  if not F.is_function(ufunc) then
    error("NewField*Function() expects an Ebb Function "..
          "as the last argument", 3)
  end

  local lookup = rel[fname]
  if lookup and isfielddispatcher(lookup) then return lookup
  elseif lookup then
    error("Cannot create a new field-function with name '"..fname.."'  "..
          "That name is already being used.", 3)
  end

  rawset(rel, fname, NewFieldDispatcher())
  return rel[fname]
end

function Relation:NewFieldReadFunction(fname, userfunc)
  local dispatch = getFieldDispatcher(self, fname, userfunc)
  if dispatch._reader then
    error("NewFieldReadFunction() error: function already assigned.", 2)
  end
  dispatch._reader = userfunc
  self._functions:insert(userfunc)
  return userfunc
end

function Relation:NewFieldWriteFunction(fname, userfunc)
  local dispatch = getFieldDispatcher(self, fname, userfunc)
  if dispatch._writer then
    error("NewFieldWriteFunction() error: function already assigned.", 2)
  end
  dispatch._writer = userfunc
  self._functions:insert(userfunc)
  return userfunc
end

local redops = {
  ['+'] = true,
  ['-'] = true,
  ['*'] = true,
  ['max'] = true,
  ['min'] = true,
}
function Relation:NewFieldReduceFunction(fname, op, userfunc)
  local dispatch = getFieldDispatcher(self, fname, userfunc)
  if not redops[op] then
    error("NewFieldReduceFunction() expects a reduction operator as the "..
          "second argument.", 2)
  end
  if dispatch._reducers[op] then
    error("NewFieldReduceFunction() error: '"..op.."' "..
          "function already assigned.", 2)
  end
  dispatch._reducers[op] = userfunc
  self._functions:insert(userfunc)
  return userfunc
end

-------------------------------------------------------------------------------
--[[  Subsets                                                              ]]--
-------------------------------------------------------------------------------

function Subset:foreach(user_func, ...)
  if not F.is_function(user_func) then
    error('map(): expects an Ebb function as the argument', 2)
  end
  user_func:_doForEach(self, ...)
end

function Subset:Relation()
  return self._owner
end

function Subset:Name()
  return self._name
end

function Subset:FullName()
  return self._owner._name .. '.' .. self._name
end

function Subset:Rectangle()
  return self._rectangle
end

-- prevent user from modifying the lua table
function Subset:__newindex(name,value)
  error("Cannot assign members to Subset object", 2)
end

local function is_int(obj)
  return type(obj) == 'number' and obj % 1 == 0
end

local function is_subrectangle(rel, obj)
  local dims = rel:Dims()
  if not terralib.israwlist(obj) or #obj ~= #dims then return false end
  for i,r in ipairs(obj) do
    if not terralib.israwlist(r) or #r ~= 2 then return false end
    if not is_int(r[1]) or not is_int(r[2]) then return false end
    if r[1] < 0 or r[2] < 0 or r[1] >= dims[i] or r[2] >= dims[i] then
      return false
    end
  end
  return true
end

function Relation:NewDivision( rects )
  if not self:isGrid() then
    error("NewDivision(): Can only be called on grid-typed relations", 2)
  end
  local division = terralib.newlist()
  for name,rect in pairs(rects) do
    if type(name) ~= "string" then
      error("NewDivision(): Subset names must be strings", 2)
    end
    if not is_valid_lua_identifier(name) then
      error(valid_name_err_msg.subset, 2)
    end
    if self[name] then
      error("Cannot create a new subset with name '"..name.."'  "..
              "That name is already being used.", 2)
    end
    if not type(rect) == 'table' or not terralib.israwlist(rect) then
      error("NewDivision(): Rectangles must be lists", 2)
    end
    if is_subrectangle(self, rect) then
      local subset = setmetatable({
        _owner     = self,
        _name      = name,
        _rectangle = rect,
      }, Subset)
      rawset(self, name, subset)
      division:insert(subset)
    end
    --if not is_subrectangle(self, rect) then
    --  error("NewDivision(): Rectangle was not a list of "..(#self:Dims())..
    --        " range pairs lying inside the grid", 2)
    --end
    ---- TODO: Assuming the rectangles are disjoint, and cover the entire grid.
    --local subset = setmetatable({
    --  _owner     = self,
    --  _name      = name,
    --  _rectangle = rect,
    --}, Subset)
    --rawset(self, name, subset)
    --division:insert(subset)
  end
  self._divisions:insert(division)
  M.decls():insert(M.AST.NewDivision(division))
end

-------------------------------------------------------------------------------
--[[  Fields                                                               ]]--
-------------------------------------------------------------------------------

-- prevent user from modifying the lua table
function Field:__newindex(name,value)
  error("Cannot assign members to Field object", 2)
end

function Field:Name()
  return self._name
end
function Field:FullName()
  return self._owner._name .. '.' .. self._name
end
function Field:Size()
  return self._owner:Size()
end
function Field:ConcreteSize()
  return self._owner:ConcreteSize()
end
function Field:Type()
  return self._type
end
function Field:Relation()
  return self._owner
end

function Relation:NewField(name, typ)
  if not name or type(name) ~= "string" then
    error("NewField() expects a string as the first argument", 2)
  end
  if not is_valid_lua_identifier(name) then
    error(valid_name_err_msg.field, 2)
  end
  if self[name] then
    error("Cannot create a new field with name '"..name.."'  "..
          "That name is already being used.", 2)
  end
  if string.sub(name, 1, 2) == '__' then
    error("Field names starting with '__' are reserved by the system.", 2)
  end

  if is_relation(typ) then
    typ = T.key(typ)
  end
  if not T.istype(typ) or not typ:isfieldvalue() then
    error("NewField() expects an Ebb type or "..
          "relation as the 2nd argument", 2)
  end
  if typ:iskey() and typ.relation:isCoupled() then
    error("Foreign keys to coupled relations are not allowed", 2)
  end

  -- create the field
  local field   = setmetatable({
    _type   = typ,
    _name   = name,
    _owner  = self,
  }, Field)
  rawset(self, name, field)

  self._fields:insert(field)

  M.decls():insert(M.AST.NewField(field))

  return field
end

function Field:Fill(val)
  if not T.luaValConformsToType(val, self._type) then
    error('Value to be loaded does not match field type', 2)
  end
  M.stmts():insert(M.AST.FillField(self, val))
end

-------------------------------------------------------------------------------
--[[  Input/output                                                         ]]--
-------------------------------------------------------------------------------

function Relation:Dump(flds, file, ...)
  local args = terralib.newlist({...}):map(function(x)
    return M.isExprConst(x) and M.AST.Const(x) or x
  end)
  M.stmts():insert(M.AST.Dump(self, terralib.newlist(flds), file, args))
end

function Relation:Load(flds, file, ...)
  local args = terralib.newlist({...}):map(function(x)
    return M.isExprConst(x) and M.AST.Const(x) or x
  end)
  M.stmts():insert(M.AST.Load(self, terralib.newlist(flds), file, args))
end
