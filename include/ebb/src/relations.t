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
local AL    = require "ebb.src.api_log"

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
function Relation:isPlain()       return self._mode == 'PLAIN'      end
function Relation:isGrid()        return self._mode == 'GRID'       end

-- Create a generic relation
-- local myrel = L.NewRelation {
--   name = 'myrel',
--   mode = 'PLAIN',
--  [size = 35,]        -- IF mode ~= 'GRID'
--  [dims = {45,90}, ]  -- IF mode == 'GRID'
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
  if mode ~= 'PLAIN' and mode ~= 'GRID'  and mode ~= 'ELASTIC' then
    error("NewRelation(): Bad 'mode' argument.  Was expecting\n"..
          "  PLAIN, GRID, or ELASTIC", 2)
  end
  if mode == 'GRID' then
    if type(params.dims) ~= 'table' or
       (#params.dims ~= 2 and #params.dims ~= 3)
    then
      error("NewRelation(): Grids must specify 'dim' argument; "..
            "a table of 2 to 3 numbers specifying grid size", 2)
    end
    if params.periodic then
      if type(params.periodic) ~= 'table' then
        error("NewRelation(): 'periodic' argument must be a list", 2)
      elseif #params.periodic ~= #params.dims then
        error("NewRelation(): periodicity is specified for "..
              tostring(#params.periodic).." dimensions; does not match "..
              tostring(#params.dims).." dimensions specified", 2)
      end
    end
  else
    if type(params.size) ~= 'number' then
      error("NewRelation() expects 'size' numeric argument", 2)
    end
  end

  -- CONSTRUCT and return the relation
  local rel = setmetatable( {
    _name      = params.name,
    _mode      = mode,
    _uid       = relation_uid,

    _fields    = terralib.newlist(),
    _subsets   = terralib.newlist(),
    _macros    = terralib.newlist(),
    _functions = terralib.newlist(),

    _incoming_refs = {}, -- used for walking reference graph
    _disjoint_partition = nil
  },
  Relation)
  relation_uid = relation_uid + 1 -- increment unique id counter

  -- store mode dependent values
  local size = params.size
  if mode == 'GRID' then
    size = 1
    rawset(rel, '_dims', {})
    rawset(rel, '_periodic', {})
    for i,n in ipairs(params.dims) do
      rel._dims[i]    = n
      size            = size * n
      if params.periodic and params.periodic[i] then rel._periodic = true
                                                else rel._periodic = false end
    end
  end
  rawset(rel, '_logical_size',  size)
  AL.RecordAPICall('NewRelation', params, rel)
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

function Relation:foreach(user_func, ...)
  if not is_function(user_func) then
    error('foreach(): expects an ebb function as the first argument', 2)
  end
  user_func:_doForEach(self, ...)
end

function Relation:hasSubsets()
  return #self._subsets ~= 0
end

-- prevent user from modifying the lua table
function Relation:__newindex(fieldname,value)
  error("Cannot assign members to Relation object "..
      "(did you mean to call relation:New...?)", 2)
end

function Relation:NewFieldMacro (name, macro)
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

function Relation:_INTERNAL_NewSubsetFromRectangles(name, rectangles)
  AL.RecordAPICall('NewRectangleSubset', {self, name, rectangles}, nil)
end

function Relation:NewSubset( name, arg )
  if not name or type(name) ~= "string" then
    error("NewSubset() expects a string as the first argument", 2) end
  if not is_valid_lua_identifier(name) then
    error(valid_name_err_msg.subset, 2) end
  if self[name] then
    error("Cannot create a new subset with name '"..name.."'  "..
          "That name is already being used.", 2)
  end
  if type(arg) == 'table' then
    if self:isGrid() then
      if arg.rectangles then
        if not terralib.israwlist(arg.rectangles) then
          error("NewSubset(): Was expecting 'rectangles' to be a list", 2)
        end
        for i,r in ipairs(arg.rectangles) do
          if not is_subrectangle(self, r) then
            error("NewSubset(): Entry #"..i.." in 'rectangles' list was "..
                  "not a rectangle, specified as a list of "..(#self:Dims())..
                  " range pairs lying inside the grid", 2)
          end
        end
        return self:_INTERNAL_NewSubsetFromRectangles(name, arg.rectangles)
      else -- assume a single rectangle
        if not is_subrectangle(self, arg) then
          error('NewSubset(): Was expecting a rectangle specified as a '..
                'list of '..(#self:Dims())..' range pairs lying inside '..
                'the grid', 2)
        end
        return self:_INTERNAL_NewSubsetFromRectangles(name, { arg })
      end
    end
  else
    error("Unexpected argument to subsets.", 2)
  end
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

function Relation:NewField (name, typ)  
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
  
  if is_relation(typ) then
    typ = keyT(typ)
  end
  if not T.istype(typ) or not typ:isfieldvalue() then
    error("NewField() expects an Ebb type or "..
          "relation as the 2nd argument", 2)
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

  AL.RecordAPICall('NewField', {self, name, typ}, field)

  return field
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

function Field:Load(val)
  if not T.luaValConformsToType(val, self._type) then
    error('Value to be loaded does not match field type', 2)
  end
  AL.RecordAPICall('LoadField', { self, val }, nil)
end


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--[[  Partitioning relations                                               ]]--
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

function Relation:SetPartitions(num_partitions)
  AL.RecordAPICall('SetPartitions', {self, num_partitions}, nil)
end
