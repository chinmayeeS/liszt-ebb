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

-- file/module namespace table
local R = {}
package.loaded["ebb.src.relations"] = R

local Pre   = require "ebb.src.prelude"
local T     = require "ebb.src.types"
local F     = require "ebb.src.functions"
local M     = require "ebb.src.main"

local keyT      = T.key

local is_macro      = Pre.is_macro
local is_function   = F.is_function


local PN = require "ebb.lib.pathname"

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


-------------------------------------------------------------------------------
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
-------------------------------------------------------------------------------
--[[  Relation methods                                                     ]]--
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------


-- A Relation can be in at most one of the following MODES
--    PLAIN
--    GRID
--    FLEXIBLE
function Relation:isPlain()       return self._mode == 'PLAIN'      end
function Relation:isGrid()        return self._mode == 'GRID'       end
function Relation:isFlexible()    return self._mode == 'FLEXIBLE'   end

-- Create a generic relation
-- local myrel = L.NewRelation {
--   name = 'myrel',
--   mode = 'PLAIN' | 'GRID' | 'FLEXIBLE',
--   -- if mode == 'PLAIN':
--   size = 35,
--   -- if mode == 'GRID':
--   dims = {45,90},
--   -- if mode == 'FLEXIBLE':
--   size = 100,
--   max_skew = 3.0,
--   max_xfer_rate = 0.3,
--   xfer_stencil = {{0,0,1},{0,0,-1},...},
-- }
local relation_uid = 0
function R.NewRelation(params)
  -- CHECK the parameters coming in
  if type(params) ~= 'table' then
    error("NewRelation() expects a table of named arguments", 2)
  elseif type(params.name) ~= 'string' then
    error("NewRelation() expects 'name' string argument", 2)
  end
  if not is_valid_lua_identifier(params.name) then
    error(valid_name_err_msg.relation, 2)
  end
  local mode = params.mode or 'PLAIN'
  if not params.mode and params.dims then mode = 'GRID' end
  if mode ~= 'PLAIN' and mode ~= 'GRID' and mode ~= 'FLEXIBLE' then
    error("NewRelation(): Bad 'mode' argument.  Was expecting\n"..
          "  PLAIN, GRID or FLEXIBLE", 2)
  end
  if mode == 'PLAIN' then
    if type(params.size) ~= 'number' then
      error("NewRelation() expects 'size' numeric argument", 2)
    end
  elseif mode == 'GRID' then
    if type(params.dims) ~= 'table' or
       (#params.dims ~= 2 and #params.dims ~= 3)
    then
      error("NewRelation(): Grids must specify 'dim' argument; "..
            "a table of 2 to 3 numbers specifying grid size", 2)
    end
  elseif mode == 'FLEXIBLE' then
    if type(params.size) ~= 'number' then
      error("NewRelation() expects 'size' numeric argument", 2)
    end
    if type(params.max_skew) ~= 'number' then
      error("NewRelation() expects 'max_skew' numeric argument", 2)
    end
    if type(params.max_xfer_rate) ~= 'number' then
      error("NewRelation() expects 'max_xfer_rate' numeric argument", 2)
    end
    if not terralib.israwlist(params.xfer_stencil) then
      error("NewRelation(): 'xfer_stencil' argument must be a list", 2)
    end
    for _,dir in ipairs(params.xfer_stencil) do
      if (not terralib.israwlist(dir) or #dir ~= 3 or type(dir[1]) ~= 'number'
          or type(dir[2]) ~= 'number' or type(dir[3]) ~= 'number') then
        error("NewRelation(): Each element of 'xfer_stencil' argument must "..
              "be a list of 3 integers", 2)
      end
    end
  else assert(false) end

  -- CONSTRUCT and return the relation
  local rel = setmetatable( {
    _name       = params.name,
    _mode       = mode,
    _uid        = relation_uid,

    _fields     = terralib.newlist(),
    _divisions  = terralib.newlist(),
    _macros     = terralib.newlist(),
    _functions  = terralib.newlist(),

    _auto_part_fld = nil,
    _incoming_refs = {}, -- used for walking reference graph
  },
  Relation)
  relation_uid = relation_uid + 1 -- increment unique id counter

  -- store mode dependent values
  local size
  if mode == 'PLAIN' then
    size = params.size
  elseif mode == 'GRID' then
    size = 1
    rawset(rel, '_dims', {})
    for i,n in ipairs(params.dims) do
      rel._dims[i]    = n
      size            = size * n
    end
  elseif mode == 'FLEXIBLE' then
    size = params.size
    rawset(rel, '_max_skew', params.max_skew)
    rawset(rel, '_max_xfer_rate', params.max_xfer_rate)
    rawset(rel, '_xfer_stencil', terralib.newlist(params.xfer_stencil))
  end
  rawset(rel, '_logical_size',  size)

  M.decls():insert(M.AST.NewRelation(rel))
  return rel
end

function Relation:_INTERNAL_UID()
  return self._uid
end
function Relation:Size()
  return self._logical_size
end
function Relation:Name()
  return self._name
end
function Relation:Mode()
  return self._mode
end
function Relation:Fields()
  return self._fields
end
function Relation:Divisions()
  return self._divisions
end
function Relation:AutoPartitionField()
  return self._auto_part_fld
end
function Relation:Dims()
  if not self:isGrid() then
    return { self:Size() }
  end
  local dimret = {}
  for i,n in ipairs(self._dims) do dimret[i] = n end
  return dimret
end
function Relation:Periodic()
  if not self:isGrid() then return { false } end
  local wraps = {}
  for i,p in ipairs(self._dims) do wraps[i] = p end
  return wraps
end
function Relation:MaxSkew()
  return self._max_skew
end
function Relation:MaxXferRate()
  return self._max_xfer_rate
end
function Relation:XferStencil()
  return self._xfer_stencil
end

function Relation:foreach(user_func, ...)
  if not is_function(user_func) then
    error('foreach(): expects an ebb function as the first argument', 2)
  end
  user_func:_doForEach(self, ...)
end

-- prevent user from modifying the lua table
function Relation:__newindex(fieldname,value)
  error("Cannot assign members to Relation object "..
      "(did you mean to call relation:New...?)", 2)
end

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

  if not is_macro(macro) then
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
  if not is_function(ufunc) then
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
-------------------------------------------------------------------------------
--[[  Subsets:                                                             ]]--
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------


function Subset:foreach(user_func, ...)
  if not is_function(user_func) then
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
-------------------------------------------------------------------------------
--[[  Fields:                                                              ]]--
-------------------------------------------------------------------------------
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
    typ = keyT(typ)
  end
  if not T.istype(typ) or not typ:isfieldvalue() then
    error("NewField() expects an Ebb type or "..
          "relation as the 2nd argument", 2)
  end
  if typ:iskey() and typ.relation:isFlexible() then
    error("Foreign keys to flexible relations are not allowed", 2)
  end

  -- create the field
  local field   = setmetatable({
    _type   = typ,
    _name   = name,
    _owner  = self,
  }, Field)
  rawset(self, name, field)

  self._fields:insert(field)

  -- record reverse pointers for key-field references
  if typ:iskey() then
    typ:basetype().relation._incoming_refs[field] = 'key_field'
  end

  M.decls():insert(M.AST.NewField(field))

  return field
end

function Field:AutoPartitionByPreimage()
  if self._owner:isGrid() then
    error("Auto-partitioning not supported for grid-typed relations", 2)
  end
  if not self._type:iskey() then
    error("Preimage auto-partitioning requires a key-typed field", 2)
  end
  rawset(self._owner, '_auto_part_fld', self)
  -- check for cycles
  local visited = {} -- set(Relation)
  local rel = self._owner
  while true do
    if visited[rel] then
      error("Detected cycle in auto-partition directives", 2)
    end
    visited[rel] = true
    if rel._auto_part_fld then
      rel = rel._auto_part_fld:Type().relation
    else
      break
    end
  end
end

-------------------------------------------------------------------------------
--[[  Error Checking subroutines                                           ]]--

-- modular error checking
local function ferrprefix(level)
  local blob = debug.getinfo(level)
  local name = type(blob.name) == 'string' and blob.name..': ' or ''
  return name
end
local function argcheck_loadval_type(obj,typ,lvl)
  if not T.luaValConformsToType(obj,typ) then
    lvl = (lvl or 1) + 1
    error(ferrprefix(lvl).."lua value does not conform to type "..
                           tostring(typ), lvl)
  end
end

-------------------------------------------------------------------------------
--[[  High-Level Loading and Dumping Operations (Lua and Terra)            ]]--

function Field:Fill(val)
  if not T.luaValConformsToType(val, self._type) then
    error('Value to be loaded does not match field type', 2)
  end
  M.stmts():insert(M.AST.FillField(self, val))
end

function Relation:Dump(flds, file, ...)
  M.stmts():insert(M.AST.Dump(self, terralib.newlist(flds),
                              file, terralib.newlist({...})))
end

function Relation:Load(flds, file, ...)
  M.stmts():insert(M.AST.Load(self, terralib.newlist(flds),
                              file, terralib.newlist({...})))
end
