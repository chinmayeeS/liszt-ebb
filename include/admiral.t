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

local A = {}
package.loaded["admiral"] = A

import 'ebb'
import 'regent'

local AST = require 'ebb.src.ast'
local C   = require 'ebb.src.c'
local F   = require 'ebb.src.functions'
local L   = require 'ebblib'
local M   = require 'ebb.src.main'
local P   = require 'ebb.src.phase'
local R   = require 'ebb.src.relations'
local RG  = regentlib
local S   = require 'ebb.src.semant'
local T   = require 'ebb.src.types'

local newlist = terralib.newlist

-------------------------------------------------------------------------------
-- Parse config options
-------------------------------------------------------------------------------

-- string -> bool
local function exists(filename)
  return os.rename(filename, filename) and true or false
end

local DEBUG = os.getenv('DEBUG') == '1'

local SAVEOBJ = os.getenv('SAVEOBJ') == '1'

local OBJNAME = os.getenv('OBJNAME') or 'a.out'

local USE_HDF = not (os.getenv('USE_HDF') == '0')

local HDF_HEADER
if USE_HDF then
  if exists('/usr/include/hdf5/serial') then
    HDF_HEADER = 'hdf5/serial/hdf5.h'
  else
    HDF_HEADER = 'hdf5.h'
  end
end

local LIBS = newlist({'-lm'})
if USE_HDF then
  if exists('/usr/include/hdf5/serial') then
    terralib.linklibrary('libhdf5_serial.so')
    LIBS:insert('-lhdf5_serial')
  else
    terralib.linklibrary('libhdf5.so')
    LIBS:insertall {'-L/usr/lib/x86_64-linux-gnu', '-lhdf' }
  end
end

local function primPartDims()
  local dop = RG.config['parallelize-dop']
  local NX,NY,NZ = dop:match('^(%d+),(%d+),(%d+)$')
  if NX then
    return tonumber(NX),tonumber(NY),tonumber(NZ)
  end
  local num = assert(tonumber(dop))
  local factors = newlist()
  while num > 1 do
    for p = 2, num do
      if num % p == 0 then
        factors:insert(p)
        num = num / p
        break
      end
    end
  end
  NX,NY,NZ = 1,1,1
  for i = 1, #factors do
    if i % 3 == 1 then NX = NX * factors[i] end
    if i % 3 == 2 then NY = NY * factors[i] end
    if i % 3 == 0 then NZ = NZ * factors[i] end
  end
  return NX,NY,NZ
end
local NX,NY,NZ = primPartDims()
local NUM_PRIM_PARTS = NX * NY * NZ

-------------------------------------------------------------------------------
-- Helper functions
-------------------------------------------------------------------------------

local function quit(obj)
  print('====================')
  print('Unsupported class:')
  if not obj then
    print('Nil')
  elseif obj.kind then
    print(obj.kind)
  else
    print('(no kind information)')
  end
  print('--------------------')
  while obj do
    for k,_ in pairs(obj) do
      print(k)
    end
    print('--------------------')
    obj = getmetatable(obj)
  end
  assert(false)
end

-- terralib.type -> number
local function minValue(T)
  return
    (T == int)    and -2147483648 or
    (T == int8)   and -128 or
    (T == int16)  and -32768 or
    (T == int32)  and -2147483648 or
    (T == int64)  and -9223372036854775808 or
    (T == uint)   and 0 or
    (T == uint8)  and 0 or
    (T == uint16) and 0 or
    (T == uint32) and 0 or
    (T == uint64) and 0 or
    (T == bool)   and 0 or
    (T == float)  and -math.huge or
    (T == double) and -math.huge or
    assert(false)
end

-- terralib.type -> number
local function maxValue(T)
  return
    (T == int)    and 2147483647 or
    (T == int8)   and 127 or
    (T == int16)  and 32767 or
    (T == int32)  and 2147483647 or
    (T == int64)  and 9223372036854775807 or
    (T == uint)   and 4294967295 or
    (T == uint8)  and 255 or
    (T == uint16) and 65535 or
    (T == uint32) and 4294967295 or
    (T == uint64) and 18446744073709551615 or
    (T == bool)   and 1 or
    (T == float)  and math.huge or
    (T == double) and math.huge or
    assert(false)
end

-- string, terralib.type -> number
local function opIdentity(op, T)
  return
    (op == '+')   and 0 or
    (op == '-')   and 0 or
    (op == '*')   and 1 or
    (op == '/')   and 1 or
    (op == 'max') and minValue(T) or
    (op == 'min') and maxValue(T) or
    assert(false)
end

-- string -> string
local function opName(op)
  return
    (op == '+')   and 'add' or
    (op == '-')   and 'sub' or
    (op == '*')   and 'mul' or
    (op == '/')   and 'div' or
    (op == 'max') and 'max' or
    (op == 'min') and 'min' or
    assert(false)
end

-- (* -> *) -> ()
local function prettyPrintFun(fun)
  local raw = fun:prettystring(false)
  local startIdx
  for line in raw:gmatch('[^\n]+') do
    if not startIdx then
      local a,b = line:find('%S+')
      startIdx = b + 2
    end
    if not line:find('debuginfo') then
      print(line:sub(startIdx))
    end
  end
end

-- RG.Task -> ()
local function prettyPrintTask(tsk)
  tsk:printpretty()
end

-- terralib.struct -> ()
local function prettyPrintStruct(s)
  print('struct '..s.name..' {')
  for _,e in ipairs(s.entries) do
    print('  '..e.field..' : '..tostring(e.type)..';')
  end
  print('}')
end

-- string -> string
local function idSanitize(s)
  return s:gsub('[^%w]', '_')
end

local NAME_CACHE = {} -- map(string, (* -> *) | RG.task)

-- RG.task, string -> ()
local function setTaskName(tsk, name)
  name = idSanitize(name)
  while NAME_CACHE[name] do
    name = name..'_'
  end
  NAME_CACHE[name] = tsk
  tsk:setname(name)
  tsk.ast.name[1] = name -- TODO: Dangerous
end

-- (* -> *), string -> ()
local function setFunName(fun, name)
  name = idSanitize(name)
  while NAME_CACHE[name] do
    name = name..'_'
  end
  NAME_CACHE[name] = fun
  fun:setname(name)
end

local TerraList = getmetatable(newlist())

-- () -> T*
function TerraList:copy()
  return self:map(function(x) return x end)
end

-- T -> int?
function TerraList:find(x)
  for i,elem in ipairs(self) do
    if elem == x then
      return i
    end
  end
  return nil
end

-- () -> set(T)
function TerraList:toSet()
  local set = {}
  for _,elem in ipairs(self) do
    set[elem] = true
  end
  return set
end

-- string? -> string
function TerraList:join(sep)
  sep = sep or ' '
  local res = ''
  for i,elem in ipairs(self) do
    if i > 1 then
      res = res..sep
    end
    res = res..tostring(elem)
  end
  return res
end

-- () -> T*
function TerraList:reverse()
  local res = newlist()
  for i = #self, 1, -1 do
    res:insert(self[i])
  end
  return res
end

-- () -> T
function TerraList:pop()
  local res = self[#self]
  self[#self] = nil
  return res
end

-- table -> bool
local function isEmpty(tab)
  if not tab then
    return true
  end
  for _,_ in pairs(tab) do
    return false
  end
  return true
end

-- map(K,V) -> K*
local function keys(map)
  local res = newlist()
  for k,v in pairs(map) do
    res:insert(k)
  end
  return res
end

-------------------------------------------------------------------------------
-- Vector type support
-------------------------------------------------------------------------------

-- terralib.type, int -> terralib.type
local Vector = terralib.memoize(function(T, N)
  return T[N]
end)

-- T:terralib.type, N:int -> (Vector(T,N), Vector(T,N) -> T)
local emitDotProduct = terralib.memoize(function(T, N)
  local a = symbol(Vector(T,N), 'a')
  local b = symbol(Vector(T,N), 'b')
  local elems = newlist()
  local expr = `(a[0] * b[0])
  for i=1,N-1 do
    expr = `expr + (a[ [i] ] * b[ [i] ])
  end
  local terra dot([a], [b]) : T
    return [expr]
  end
  setFunName(dot, 'dot_'..tostring(T)..'_'..tostring(N))
  if DEBUG then prettyPrintFun(dot) end
  return dot
end)

-- string, T:terralib.type, N:int -> (Vector(T,N), T -> Vector(T,N))
local emitVectorVectorOp = terralib.memoize(function(op, T, N)
  local a = symbol(Vector(T,N), 'a')
  local b = symbol(Vector(T,N), 'b')
  local elems = newlist()
  for i=0,N-1 do
    elems:insert((op == '+') and (`a[ [i] ] + b[ [i] ]) or
                 (op == '-') and (`a[ [i] ] - b[ [i] ]) or
                 (op == '*') and (`a[ [i] ] * b[ [i] ]) or
                 (op == '/') and (`a[ [i] ] / b[ [i] ]) or
                 (op == '%') and (`a[ [i] ] % b[ [i] ]) or
                 assert(false))
  end
  local terra vvop([a], [b]) : Vector(T,N)
    return array([elems])
  end
  setFunName(vvop, 'vv_'..opName(op)..'_'..tostring(T)..'_'..tostring(N))
  if DEBUG then prettyPrintFun(vvop) end
  return vvop
end)

-- string, T:terralib.type, N:int -> (Vector(T,N), T -> Vector(T,N))
local emitVectorScalarOp = terralib.memoize(function(op, T, N)
  local a = symbol(Vector(T,N), 'a')
  local b = symbol(T, 'b')
  local elems = newlist()
  for i=0,N-1 do
    elems:insert((op == '+') and (`a[ [i] ] + b) or
                 (op == '-') and (`a[ [i] ] - b) or
                 (op == '*') and (`a[ [i] ] * b) or
                 (op == '/') and (`a[ [i] ] / b) or
                 (op == '%') and (`a[ [i] ] % b) or
                 assert(false))
  end
  local terra vsop([a], [b]) : Vector(T,N)
    return array([elems])
  end
  setFunName(vsop, 'vs_'..opName(op)..'_'..tostring(T)..'_'..tostring(N))
  if DEBUG then prettyPrintFun(vsop) end
  return vsop
end)

-- terralib.type, RG.rexpr* -> RG.rexpr
local function emitVectorCtor(T, elems)
  return rexpr array([elems]) end
end

-------------------------------------------------------------------------------
-- Translation helper functions
-------------------------------------------------------------------------------

-- () -> bool
function F.Function:isKernel()
  return (#self._decl_ast.params == 1 and
          self._decl_ast.ptypes[1]:iskey() and
          not self._decl_ast.exp)
end

-- map(B.Builtin, (double -> double))
local UNARY_ARITH_FUNS = {
  [L.acos]  = RG.acos(double),
  [L.asin]  = RG.asin(double),
  [L.atan]  = RG.atan(double),
  [L.cbrt]  = RG.cbrt(double),
  [L.ceil]  = RG.ceil(double),
  [L.cos]   = RG.cos(double),
  [L.fabs]  = RG.fabs(double),
  [L.floor] = RG.floor(double),
  [L.log]   = RG.log(double),
  [L.sin]   = RG.sin(double),
  [L.sqrt]  = RG.sqrt(double),
  [L.tan]   = RG.tan(double),
}

-- map(B.Builtin, (double, double -> double))
local BINARY_ARITH_FUNS = {
  [L.pow]   = RG.pow(double),
  [L.fmod]  = RG.fmod(double),
}

-- T.Type -> terralib.type
local function toRType(typ)
  if typ:isprimitive() then
    return typ:terratype()
  elseif typ:isvector() then
    return Vector(toRType(typ.type), typ.N)
  elseif typ:ismatrix() then
    -- TODO: Not supporting matrix types, or operations
    assert(false)
  elseif typ:iskey() then
    return typ.relation:indexType()
  else assert(false) end
end

-- M.ExprConst -> T.Type
local function inferType(lit)
  if type(lit) == 'boolean' then
    return L.bool
  elseif type(lit) == 'number' then
    if lit == math.floor(lit) then
      return L.int
    else
      return L.double
    end
  elseif type(lit) == 'table' then
    assert(terralib.israwlist(lit))
    assert(#lit > 0)
    return L.vector(inferType(lit[1]), #lit)
  else assert(false) end
end

-- M.ExprConst, T.Type? -> RG.rexpr
local function toRConst(lit, typ)
  typ = typ or inferType(lit)
  if typ:iskey() then
    return typ.relation:translateIndex(lit)
  elseif type(lit) == 'boolean' then
    assert(typ == L.bool)
    return rexpr lit end
  elseif type(lit) == 'number' then
    return rexpr [toRType(typ)](lit) end
  elseif type(lit) == 'table' then
    -- TODO: Not supporting matrix types, or operations
    assert(typ:isvector())
    assert(terralib.israwlist(lit))
    assert(#lit == typ.N)
    return emitVectorCtor(
      toRType(typ.type),
      newlist(lit):map(function(e) return toRConst(e, typ.type) end))
  else assert(false) end
end

-- string, T.Type, RG.rexpr, RG.rexpr -> RG.rquote
local function emitReduce(op, typ, lval, exp)
  assert(op ~= '/' or typ == L.float or typ == L.double)
  if typ:isvector() then
    local tmp = RG.newsymbol(toRType(typ), 'tmp')
    local v = RG.newsymbol(toRType(typ), 'v')
    local stmts = newlist()
    stmts:insert(rquote var [tmp] = exp end)
    stmts:insert(rquote var [v] = lval end)
    for i=0,typ.N-1 do
      stmts:insert(
        (op == '+')   and rquote v[ [i] ] +=   tmp[ [i] ]     end or
        (op == '-')   and rquote v[ [i] ] +=   -tmp[ [i] ]    end or
        (op == '*')   and rquote v[ [i] ] *=   tmp[ [i] ]     end or
        (op == '/')   and rquote v[ [i] ] *=   1.0/tmp[ [i] ] end or
        (op == 'max') and rquote v[ [i] ] max= tmp[ [i] ]     end or
        (op == 'min') and rquote v[ [i] ] min= tmp[ [i] ]     end or
        assert(false))
    end
    stmts:insert(rquote lval = v end)
    return rquote [stmts] end
  end
  return
    (op == '+')   and rquote lval +=   exp     end or
    (op == '-')   and rquote lval +=   -exp    end or
    (op == '*')   and rquote lval *=   exp     end or
    (op == '/')   and rquote lval *=   1.0/exp end or
    (op == 'max') and rquote lval max= exp     end or
    (op == 'min') and rquote lval min= exp     end or
    assert(false)
end

-- RG.rexpr, AST.Expression -> RG.rexpr
local function emitIndexExpr(base, index)
  assert(index:is(AST.Number))
  assert(index.node_type == L.int)
  return rexpr base[ [index.value] ] end
end

-------------------------------------------------------------------------------
-- Relation-to-region translation
-------------------------------------------------------------------------------

-- () -> RG.index_type
function R.Relation:indexType()
  if not self:isGrid() then return ptr end
  local dims = self:Dims()
  return
    (not self:isGrid()) and ptr   or
    (#dims == 1)        and int1d or
    (#dims == 2)        and int2d or
    (#dims == 3)        and int3d or
    assert(false)
end

-- () -> (uint64[K] -> intKd)
R.Relation.emitVectorToIndexType = terralib.memoize(function(self)
  local dims = self:Dims()
  local indexType = self:indexType()
  local vec2idx
  if not self:isGrid() or #dims == 1 then
    terra vec2idx(v : uint64[1])
      return [indexType]({__ptr = [indexType.impl_type](v[0])})
    end
  elseif #dims == 2 then
    terra vec2idx(v : uint64[2])
      return [indexType]({__ptr = [indexType.impl_type]{v[0], v[1]}})
    end
  elseif #dims == 3 then
    terra vec2idx(v : uint64[3])
      return [indexType]({__ptr = [indexType.impl_type]{v[0], v[1], v[2]}})
    end
  else assert(false) end
  setFunName(vec2idx, 'vec'..tostring(#dims)..'d_to_idx')
  if DEBUG then prettyPrintFun(vec2idx) end
  return vec2idx
end)

-- () -> RG.ispace_type
function R.Relation:indexSpaceType()
  return ispace(self:indexType())
end

-- () -> terralib.struct
R.Relation.fieldSpace = terralib.memoize(function(self)
  local fs = terralib.types.newstruct(self:Name() .. '_columns')
  for _,fld in ipairs(self:Fields()) do
    fs.entries:insert({field=fld:Name(), type=toRType(fld:Type())})
  end
  if self:isFlexible() then
    fs.entries:insert({field='__valid', type=bool})
  end
  if DEBUG then prettyPrintStruct(fs) end
  return fs
end)

-- () -> RG.region_type
function R.Relation:regionType()
  -- Region types in signatures must be distinct, so we're not caching here.
  return region(self:indexSpaceType(), self:fieldSpace())
end

-- M.ExprConst -> RG.rexpr
function R.Relation:translateIndex(lit)
  local dims = self:Dims()
  local indexType = self:indexType()
  if not self:isGrid() or #dims == 1 then
    return rexpr [indexType]([toRConst(lit, L.int)]) end
  elseif #dims == 2 then
    assert(terralib.israwlist(lit))
    assert(#lit == 2)
    return rexpr [indexType]({ x = [toRConst(lit[1], L.int)],
                               y = [toRConst(lit[2], L.int)]}) end
  elseif #dims == 3 then
    assert(terralib.israwlist(lit))
    assert(#lit == 3)
    return rexpr [indexType]({ x = [toRConst(lit[1], L.int)],
                               y = [toRConst(lit[2], L.int)],
                               z = [toRConst(lit[3], L.int)]}) end
  else assert(false) end
end

-- () -> int
function R.Relation:primPartSize()
  assert(self:isFlexible() and self:AutoPartitionField())
  -- In this case, we make sure all sub-partitions are of the same size.
  return math.ceil(math.ceil(self:Size() / NUM_PRIM_PARTS) * self:MaxSkew())
end

-- () -> RG.rexpr
function R.Relation:emitISpaceInit()
  if RG.config['parallelize'] and self:isFlexible()
       and self:AutoPartitionField() then
    return rexpr ispace(ptr, [self:primPartSize()] * NUM_PRIM_PARTS) end
  end
  local dims = self:Dims()
  local indexType = self:indexType()
  return
    (not self:isGrid() or #dims == 1) and rexpr
      ispace(indexType, [dims[1]])
    end or
    (#dims == 2) and rexpr
      ispace(indexType, { x = [dims[1]], y = [dims[2]] })
    end or
    (#dims == 3) and rexpr
      ispace(indexType, { x = [dims[1]], y = [dims[2]], z = [dims[3]] })
    end or
    assert(false)
end

-- RG.symbol -> RG.rquote
function R.Relation:emitRegionInit(rg)
  local ispaceExpr = self:emitISpaceInit()
  local fspaceExpr = self:fieldSpace()
  local declQuote = rquote var [rg] = region(ispaceExpr, fspaceExpr) end
  local allocQuote = rquote end
  if not self:isGrid() then
    allocQuote = rquote new(ptr(fspaceExpr, rg), [self:Dims()[1]]) end
  end
  local fillQuote = rquote end
  if self:isFlexible() then
    fillQuote = rquote fill(rg.__valid, false) end
  end
  return rquote
    [declQuote];
    [allocQuote];
    [fillQuote]
  end
end

-- RG.symbol, RG.symbol, RG.symbol -> RG.rquote
function R.Relation:emitPrimPartInit(r, p, colors)
  if self:isFlexible() and self:AutoPartitionField() then
    local primPartSize = self:primPartSize()
    return rquote
      var coloring = RG.c.legion_point_coloring_create()
      for x = 0, NX do
        for y = 0, NY do
          for z = 0, NZ do
            var rBase : int64
            for rStart in r do
              rBase = __raw(rStart).value + (x*NY*NZ + y*NZ + z) * primPartSize
              break
            end
            RG.c.legion_point_coloring_add_range(
              coloring, int3d{x,y,z},
              [RG.c.legion_ptr_t]{value = rBase},
              [RG.c.legion_ptr_t]{value = rBase + primPartSize - 1})
          end
        end
      end
      var [p] = partition(disjoint, r, coloring, colors)
      RG.c.legion_point_coloring_destroy(coloring)
    end
  end
  return rquote
    var [p] = partition(equal, r, colors)
  end
end

-- () -> RG.task
R.Relation.emitElemColor = terralib.memoize(function(self)
  local dims = self:Dims()
  local elemColor
  if self:isGrid() and #dims == 3 then
    -- HACK: Reverse engineering the compiler's partioning scheme.
    __demand(__inline) task elemColor(idx : int3d)
      var blockSizeX = ([dims[1]] + NX - 1) / NX
      var blockSizeY = ([dims[2]] + NY - 1) / NY
      var blockSizeZ = ([dims[3]] + NZ - 1) / NZ
      return int3d{idx.x / blockSizeX, idx.y / blockSizeY, idx.z / blockSizeZ}
    end
  else
    -- TODO: Not covered: Non-3D grids, plain and flexible relations. The last
    -- two follow a different partitioning scheme, and may also require the
    -- base region to calculate offsets.
    assert(false)
  end
  setTaskName(elemColor, self:Name()..'_elemColor')
  if DEBUG then prettyPrintTask(elemColor) end
  return elemColor
end)

-- () -> int
function R.Relation:perDirQueueSize()
  assert(self:isFlexible() and self:AutoPartitionField())
  return math.ceil(self:primPartSize() * self:MaxXferRate())
end

-- RG.symbol -> RG.rquote
function R.Relation:emitQueueInit(q)
  assert(self:isFlexible() and self:AutoPartitionField())
  local queueSize = self:perDirQueueSize() * #self:XferStencil()
  local ispaceExpr = rexpr ispace(ptr, queueSize * NUM_PRIM_PARTS) end
  local fspaceExpr = self:fieldSpace()
  return rquote
    var [q] = region(ispaceExpr, fspaceExpr)
    new(ptr(fspaceExpr, q), queueSize * NUM_PRIM_PARTS)
    fill(q.__valid, false)
  end
end

-- () -> RG.task
R.Relation.emitQPartColorOff = terralib.memoize(function(self)
  assert(self:isFlexible() and self:AutoPartitionField())
  local qPartIdx = RG.newsymbol(nil, 'qPartIdx')
  local colorOff = RG.newsymbol(nil, 'colorOff')
  local conds = newlist()
  for i,stencil in ipairs(self:XferStencil()) do
    conds:insert(rquote
      if qPartIdx == [i-1] then
        colorOff = int3d{ [stencil[1]], [stencil[2]], [stencil[3]] }
      end
    end)
  end
  local qPartColorOff __demand(__inline) task qPartColorOff(i : int)
    var [qPartIdx] = i
    var [colorOff] = int3d{0,0,0};
    [conds]
    -- TODO: Not checking if no case applies.
    return colorOff
  end
  setTaskName(qPartColorOff, self:Name()..'_qPartColorOff')
  if DEBUG then prettyPrintTask(qPartColorOff) end
  return qPartColorOff
end)

-- RG.symbol, RG.symbol, RG.symbol, RG.symbol -> RG.rquote
function R.Relation:emitQueuePartInit(q, qpsrc, qpdst, colors)
  assert(self:isFlexible() and self:AutoPartitionField())
  local perDirQueueSize = self:perDirQueueSize()
  local qPartColorOff = self:emitQPartColorOff()
  return rquote
    var [qpsrc] = partition(equal, q, colors)
    var coloring = RG.c.legion_point_coloring_create()
    for c in colors do
      for qPartIdx = 0, [#self:XferStencil()] do
        var qPartBase : int64
        for qBase in qpsrc[(c - qPartColorOff(qPartIdx) + {NX,NY,NZ})
                           % {NX,NY,NZ}] do
          qPartBase = __raw(qBase).value + qPartIdx * perDirQueueSize
          break
        end
        RG.c.legion_point_coloring_add_range(
          coloring, c,
          [RG.c.legion_ptr_t]{value = qPartBase},
          [RG.c.legion_ptr_t]{value = qPartBase + perDirQueueSize - 1})
      end
    end
    var [qpdst] = partition(disjoint, q, coloring, colors)
    RG.c.legion_point_coloring_destroy(coloring)
  end
end

-- () -> RG.task
R.Relation.emitPush = terralib.memoize(function(self)
  assert(self:isFlexible() and self:AutoPartitionField())
  local perDirQueueSize = self:perDirQueueSize()
  local fieldSpace = self:fieldSpace()
  local push __demand(__inline) task push
    (r        : self:regionType(),
     rPtr     : ptr(fieldSpace, r),
     q        : self:regionType(),
     qPartIdx : int)
  where
    reads(r), writes(r.__valid), reads writes(q), r * q
  do
    var qPartBase : int64
    for qBase in q do
      qPartBase = __raw(qBase).value + qPartIdx * perDirQueueSize
      break
    end
    for qPtr = qPartBase, qPartBase + perDirQueueSize do
      if not q[qPtr].__valid then
        q[qPtr] = r[rPtr]
        rPtr.__valid = false
        break
      end
    end
    RG.assert(not rPtr.__valid, 'Transfer queue ran out of space')
  end
  setTaskName(push, self:Name()..'_push')
  if DEBUG then prettyPrintTask(push) end
  return push
end)

-- () -> RG.task
R.Relation.emitPushAll = terralib.memoize(function(self)
  local autoPartFld = self:AutoPartitionField()
  assert(self:isFlexible() and autoPartFld)
  local qPartColorOff = self:emitQPartColorOff()
  local rngElemColor = autoPartFld:Type().relation:emitElemColor()
  local push = self:emitPush()
  local task pushAll
    (color : int3d, r : self:regionType(), q : self:regionType())
  where
    reads(r), writes(r.__valid), reads writes(q), r * q
  do
    for rPtr in r do
      if rPtr.__valid then
        var rColor = rngElemColor(rPtr.[autoPartFld:Name()])
        if rColor ~= color then
          for qPartIdx = 0, [#self:XferStencil()] do
            if rColor ==
              (color + qPartColorOff(qPartIdx) + {NX,NY,NZ}) % {NX,NY,NZ} then
              push(r, rPtr, q,  qPartIdx)
              break
            end
          end
          RG.assert(not rPtr.__valid, 'Element moved past predicted stencil')
        end
      end
    end
  end
  setTaskName(pushAll, self:Name()..'_pushAll')
  if DEBUG then prettyPrintTask(pushAll) end
  return pushAll
end)

-- () -> RG.task
R.Relation.emitPullAll = terralib.memoize(function(self)
  assert(self:isFlexible() and self:AutoPartitionField())
  local task pullAll
    (color : int3d, r : self:regionType(), q : self:regionType())
  where
    reads writes(r), reads(q), writes(q.__valid), r * q
  do
    for qPtr in q do
      -- TODO: Check that the element is coming to the appropriate partition.
      if qPtr.__valid then
        for rPtr in r do
          if not rPtr.__valid then
            r[rPtr] = q[qPtr]
            qPtr.__valid = false
            break
          end
        end
        RG.assert(not qPtr.__valid, 'Ran out of space on sub-partition')
      end
    end
  end
  setTaskName(pullAll, self:Name()..'_pullAll')
  if DEBUG then prettyPrintTask(pullAll) end
  return pullAll
end)

-- ProgramContext -> RG.rquote
function R.Relation:emitPrimPartUpdate(ctxt)
  local fld = assert(self:AutoPartitionField())
  if self:isFlexible() then
    local pushAll = self:emitPushAll()
    local pullAll = self:emitPullAll()
    return rquote
      for c in [ctxt.primColors] do
        pushAll(c, [ctxt.primPart[self]][c], [ctxt.qSrcPart[self]][c])
      end
      for c in [ctxt.primColors] do
        pullAll(c, [ctxt.primPart[self]][c], [ctxt.qDstPart[self]][c])
      end
      -- TODO: Check that all out-queues have been emptied out.
    end
  else
    local domRg = ctxt.relMap[self]
    local domPart = ctxt.primPart[self]
    local rngPart = ctxt.primPart[fld:Type().relation]
    return rquote
      domPart = preimage(domRg, rngPart, domRg.[fld:Name()])
    end
  end
end

-- ProgramContext -> RG.rquote
function R.Relation:emitPrimPartCheck(ctxt)
  assert(self:isFlexible())
  local autoPartFld = assert(self:AutoPartitionField())
  local domPart = ctxt.primPart[self]
  local rngPart = ctxt.primPart[autoPartFld:Type().relation]
  return rquote
    for c in [ctxt.primColors] do
      for x in [domPart][c] do
        if x.__valid then
          -- TODO: This membership check is inefficient; we should do the
          -- original partitioning manually, so we know the exact limits of the
          -- sub-partitions.
          var found = false
          for y in [rngPart][c] do
            if x.[autoPartFld:Name()] == y then
              found = true
              break
            end
          end
          RG.assert(found, 'Automatic partitioning invariant violated')
        end
      end
    end
  end
end

-------------------------------------------------------------------------------
-- Function translation
-------------------------------------------------------------------------------

-- FunInfo = {
--   name           : string
--   domainRel      : R.Relation?
--   field_use      : map(R.Field, P.PhaseType)
--   global_use     : map(L.Global, P.PhaseType)
--   inserts        : map(R.Relation, AST.InsertStatement)
--   deletes        : map(R.Relation, AST.DeleteStatement)
-- }

local FunContext = {}
FunContext.__index = FunContext

-- FunInfo, AST.Symbol*, T.Type* -> FunContext
function FunContext.New(info, argNames, argTypes)
  local self = setmetatable({
    -- Symbol mappings
    localMap        = {},        -- map(AST.Symbol, RG.rexpr)
    globalMap       = {},        -- map(L.Global, RG.symbol)
    relMap          = {},        -- map(R.Relation, RG.symbol)
    -- Signature information
    domainSym       = nil,       -- RG.Symbol?
    domainRel       = nil,       -- R.Relation?
    args            = newlist(), -- RG.Symbol*
    accessedRels    = newlist(), -- R.Relation*
    readGlobals     = newlist(), -- L.Global*
    -- Field use information
    privileges      = newlist(), -- RG.privilege*
    -- Global reduction information
    reducedGlobal   = nil,       -- L.Global?
    globalReduceAcc = nil,       -- RG.symbol?
    globalReduceOp  = nil,       -- string?
  }, FunContext)
  -- Process mapped relation
  if info.domainRel then
    local rel = info.domainRel
    self.domainSym = RG.newsymbol(rel:regionType(), 'dom')
    self.domainRel = rel
    -- Mapped relation always set as first accessed relation.
    self.accessedRels:insert(rel)
    self.relMap[rel] = RG.newsymbol(rel:regionType(), rel:Name())
  end
  -- Process arguments
  for i,lsym in ipairs(argNames) do
    local T
    if i > 1 or not info.domainRel then
      -- If this is a kernel, leave the first argument untyped (it will be used
      -- as the loop variable, and not included in the signature).
      T = toRType(argTypes[i])
    end
    local rsym = RG.newsymbol(T, tostring(lsym))
    self.args:insert(rsym)
    self.localMap[lsym] = rsym
  end
  -- Process field access modes
  local fields = keys(info.field_use)
  fields:sort(function(f1,f2) return f1:FullName() < f2:FullName() end)
  for _,fld in ipairs(fields) do
    local pt = info.field_use[fld]
    local rel = fld:Relation()
    local rg = self.relMap[rel]
    if not rg then
      rg = RG.newsymbol(rel:regionType(), rel:Name())
      self.accessedRels:insert(rel)
      self.relMap[rel] = rg
    end
    -- Assuming phase checking has checked for errors
    if pt.read or pt.write then
      self.privileges:insert(RG.privilege(RG.reads, rg, fld:Name()))
    end
    if pt.write then
      self.privileges:insert(RG.privilege(RG.writes, rg, fld:Name()))
    end
    if pt.reduceop then
      if pt.centered then
        -- More liberal privileges, but avoids copying.
        self.privileges:insert(RG.privilege(RG.reads, rg, fld:Name()))
        self.privileges:insert(RG.privilege(RG.writes, rg, fld:Name()))
      else
        self.privileges:insert(
          RG.privilege(RG.reduces(pt.reduceop), rg, fld:Name()))
      end
    end
  end
  -- Process inserts and deletes
  for rel,_ in pairs(info.inserts or {}) do
    assert(not self.relMap[rel])
    local rg = RG.newsymbol(rel:regionType(), rel:Name())
    self.accessedRels:insert(rel)
    self.relMap[rel] = rg
    for _,fld in ipairs(rel:Fields()) do
      self.privileges:insert(RG.privilege(RG.reads, rg, fld:Name()))
      self.privileges:insert(RG.privilege(RG.writes, rg, fld:Name()))
    end
    self.privileges:insert(RG.privilege(RG.reads, rg, '__valid'))
    self.privileges:insert(RG.privilege(RG.writes, rg, '__valid'))
  end
  for rel,_ in pairs(info.deletes or {}) do
    local rg = assert(self.relMap[rel])
    self.privileges:insert(RG.privilege(RG.reads, rg, '__valid'))
    self.privileges:insert(RG.privilege(RG.writes, rg, '__valid'))
  end
  -- Privileges for accessing translator-added flags
  if info.domainRel and info.domainRel:isFlexible() then
    local rg = assert(self.relMap[info.domainRel])
    self.privileges:insert(RG.privilege(RG.reads, rg, '__valid'))
  end
  -- Process global access modes
  local globals = keys(info.global_use)
  globals:sort(function(g1,g2) return g1:Name() < g2:Name() end)
  for _,g in ipairs(globals) do
    local pt = info.global_use[g]
    if pt.read and not pt.reduceop then
      assert(not self.globalMap[g])
      self.globalMap[g] = RG.newsymbol(toRType(g:Type()), idSanitize(g:Name()))
      self.readGlobals:insert(g)
    elseif pt.reduceop and not pt.read then
      assert(not self.reducedGlobal)
      self.reducedGlobal = g
      self.globalReduceAcc = RG.newsymbol(toRType(g:Type()), 'acc')
      self.globalReduceOp = pt.reduceop
    else assert(false) end
  end
  return self
end

-- AST.Symbol -> RG.symbol
function FunContext:addLocal(lsym)
  assert(not self.localMap[lsym])
  local rsym = RG.newsymbol(nil, tostring(lsym))
  self.localMap[lsym] = rsym
  return rsym
end

-- AST.Symbol, RG.rexpr -> ()
function FunContext:addAlias(lsym, expr)
  assert(not self.localMap[lsym])
  self.localMap[lsym] = expr
end

-- () -> RG.symbol*
function FunContext:signature()
  local fullArgs = newlist()
  if self.domainRel then
    fullArgs:insert(self.domainSym)
  end
  for i = 1, #self.args do
    if i > 1 or not self.domainRel then
      fullArgs:insert(self.args[i])
    end
  end
  for i = 1, #self.accessedRels do
    local rel = self.accessedRels[i]
    fullArgs:insert(self.relMap[rel])
  end
  for i = 1, #self.readGlobals do
    local g = self.readGlobals[i]
    fullArgs:insert(self.globalMap[g])
  end
  return fullArgs
end

-- FunInfo -> RG.task, FunContext
function AST.UserFunction:toTask(info)
  -- self.params : AST.Symbol*
  -- self.ptypes : T.Type*
  -- self.body   : AST.Block
  -- self.exp    : AST.Expression?
  local ctxt = FunContext.New(info, self.params, self.ptypes)
  assert(not ctxt.reducedGlobal or not self.exp)
  -- Synthesize body
  local body = newlist() -- RG.quote*
  if ctxt.reducedGlobal then
    local accInitVal =
      opIdentity(ctxt.globalReduceOp, ctxt.globalReduceAcc:gettype())
    body:insert(rquote var [ctxt.globalReduceAcc] = [accInitVal] end)
  end
  local block = self.body:toRQuote(ctxt)
  if info.domainRel then
    local loopVar = ctxt.args[1]
    if info.domainRel:isFlexible() then
      local rel = ctxt.relMap[info.domainRel]
      block = rquote if [rel][loopVar].__valid then [block] end end
    end
    block = rquote for [loopVar] in [ctxt.domainSym] do [block] end end
  end
  body:insert(block)
  if ctxt.reducedGlobal then
    body:insert(rquote return [ctxt.globalReduceAcc] end)
  end
  if self.exp then
    body:insert(rquote return [self.exp:toRExpr(ctxt)] end)
  end
  -- Synthesize task
  local tsk
  if info.domainRel then
    local dom = ctxt.domainSym
    local univ = ctxt.relMap[ctxt.domainRel]
    if not RG.config['parallelize'] then
      task tsk([ctxt:signature()]) where
        dom <= univ, [ctxt.privileges]
      do [body] end
    elseif not (isEmpty(info.inserts) and isEmpty(info.deletes)) then
      -- HACK: Need to manually parallelize insertion kernels.
      -- TODO: Only handling the simple case of functions without stencils,
      -- which don't require any changes.
      for fld,pt in pairs(info.field_use) do
        assert(pt.centered)
      end
      task tsk([ctxt:signature()]) where
        dom <= univ, [ctxt.privileges]
      do [body] end
    elseif not ctxt.reducedGlobal and RG.check_cuda_available() then
      __demand(__parallel, __cuda) task tsk([ctxt:signature()]) where
        dom <= univ, [ctxt.privileges]
      do [body] end
    else
      __demand(__parallel) task tsk([ctxt:signature()]) where
        dom <= univ, [ctxt.privileges]
      do [body] end
    end
  else
    __demand(__inline) task tsk([ctxt:signature()]) where
      [ctxt.privileges]
    do [body] end
  end
  -- Finalize task
  setTaskName(tsk, info.name)
  if DEBUG then prettyPrintTask(tsk) end
  return tsk, ctxt
end

local TO_KERNEL_TASK_CACHE = {} -- map(F.Function, {RG.task,FunContext})

-- () -> RG.task, FunContext
function F.Function:toKernelTask()
  if TO_KERNEL_TASK_CACHE[self] then
    return unpack(TO_KERNEL_TASK_CACHE[self])
  end
  assert(self:isKernel())
  local argRel = self._decl_ast.ptypes[1].relation
  local info = self:_get_typechecked(42, argRel, {})
  local typedAST = info.typed_ast
  -- info : {
  --   ...
  --   typed_ast      : AST.UserFunction
  --   field_use      : map(R.Field, P.PhaseType)
  --   global_use     : map(L.Global, P.PhaseType)
  --   inserts        : map(R.Relation, AST.InsertStatement)
  --   deletes        : map(R.Relation, AST.DeleteStatement)
  -- }
  info.name = self:Name()
  info.domainRel = argRel
  local tsk, ctxt = typedAST:toTask(info)
  TO_KERNEL_TASK_CACHE[self] = {tsk, ctxt}
  return tsk, ctxt
end

local TO_HELPER_TASK_CACHE = {} -- map(F.Function, {RG.task,FunContext})

-- T.Type* -> RG.task, FunContext
function F.Function:toHelperTask(argTypes)
  -- TODO: Only caching on the function object; we assume the helper functions
  -- have a single specialization.
  if TO_HELPER_TASK_CACHE[self] then
    return unpack(TO_HELPER_TASK_CACHE[self])
  end
  local typedAST = S.check_helper_func(self, argTypes)
  local info = P.phasePass(typedAST)
  -- info : {
  --   ...
  --   field_use      : map(R.Field, P.PhaseType)
  --   global_use     : map(L.Global, P.PhaseType)
  --   inserts        : map(R.Relation, AST.InsertStatement)
  --   deletes        : map(R.Relation, AST.DeleteStatement)
  -- }
  info.name = self:Name()
  info.domainRel = nil
  typedAST.ptypes = argTypes
  local tsk, ctxt = typedAST:toTask(info)
  TO_HELPER_TASK_CACHE[self] = {tsk, ctxt}
  return tsk, ctxt
end

-------------------------------------------------------------------------------
-- AST translation
-------------------------------------------------------------------------------

-- AST.Expression, FunContext -> RG.rexpr
local function recoverHelperCall(expr, ctxt)
  -- expr.orig_func   : F.Function
  -- expr.orig_params : AST.Expression*
  local argTypes = newlist(expr.orig_params):map(function(p)
    return p.node_type
  end)
  local hTask, hCtxt = expr.orig_func:toHelperTask(argTypes)
  local actualArgs = newlist()
  for i = 1, #expr.orig_params do
    local p = expr.orig_params[i]
    actualArgs:insert(p:toRExpr(ctxt))
  end
  for i = 1, #hCtxt.accessedRels do
    local rel = hCtxt.accessedRels[i]
    actualArgs:insert(assert(ctxt.relMap[rel]))
  end
  for i = 1, #hCtxt.readGlobals do
    local g = hCtxt.readGlobals[i]
    actualArgs:insert(assert(ctxt.globalMap[g]))
  end
  return rexpr [hTask]([actualArgs]) end
end

-- FunContext -> RG.rexpr
function AST.Expression:toRExpr(ctxt)
  error('Abstract Method')
end
function AST.BinaryOp:toRExpr(ctxt)
  -- self.lhs : AST.Expression
  -- self.rhs : AST.Expression
  -- self.op  : string
  local a = self.lhs:toRExpr(ctxt)
  local b = self.rhs:toRExpr(ctxt)
  local t1 = self.lhs.node_type
  local t2 = self.rhs.node_type
  if t1:isvector() and t2:isvector() then
    local fun = emitVectorVectorOp(self.op, toRType(t1.type), t1.N)
    return rexpr fun(a, b) end
  elseif t1:isvector() and t2:isscalar() then
    local fun = emitVectorScalarOp(self.op, toRType(t2), t1.N)
    return rexpr fun(a, b) end
  elseif t1:isscalar() and t2:isvector() and self.op == '*' then
    local fun = emitVectorScalarOp(self.op, toRType(t1), t2.N)
    return rexpr fun(b, a) end
  end
  assert(t1:isscalar() and t2:isscalar())
  return
    (self.op == '==')  and rexpr a == b  end or
    (self.op == '~=')  and rexpr a ~= b  end or
    (self.op == '<')   and rexpr a < b   end or
    (self.op == '>')   and rexpr a > b   end or
    (self.op == '<=')  and rexpr a <= b  end or
    (self.op == '>=')  and rexpr a >= b  end or
    (self.op == 'or')  and rexpr a or b  end or
    (self.op == 'and') and rexpr a and b end or
    (self.op == '+')   and rexpr a + b   end or
    (self.op == '-')   and rexpr a - b   end or
    (self.op == '*')   and rexpr a * b   end or
    (self.op == '/')   and rexpr a / b   end or
    (self.op == '%')   and rexpr a % b   end or
    assert(false)
end
function AST.Bool:toRExpr(ctxt)
  -- self.value : bool
  return rexpr [self.value] end
end
function AST.Call:toRExpr(ctxt)
  -- self.func   : B.Builtin
  -- self.params : table*
  assert(L.is_builtin(self.func))
  -- Affine expression
  -- self.params[1] : AST.LuaObject
  --   .node_type.value : R.Relation
  -- self.params[2] : AST.MatrixLiteral
  --   .n       : int
  --   .m       : int
  --   .matvals : int[.n][.m]
  -- self.params[3] : AST.Expression
  if self.func == L.Affine then
    local rel = self.params[1].node_type.value
    local dims = rel:Dims()
    -- TODO: The translated expression for self.params[3] is duplicated.
    assert(self.params[2].m == self.params[2].n + 1)
    local N = self.params[2].n
    local mat = self.params[2].matvals
    -- Only allowing diagonal translation matrices.
    for i=1,N do for j=1,N do
      assert(i == j and mat[i][j] == 1 or
             i ~= j and mat[i][j] == 0)
    end end
    local base = self.params[3]:toRExpr(ctxt)
    if N == 2 then
      local x = mat[1][3]
      local y = mat[2][3]
      if x == 0 and y == 0 then
        return base
      end
      return rexpr (base + {x,y}) %
        rect2d{
          lo = int2d{ x = 0,           y = 0           },
          hi = int2d{ x = [dims[1]-1], y = [dims[2]-1] } }
      end
    elseif N == 3 then
      local x = mat[1][4]
      local y = mat[2][4]
      local z = mat[3][4]
      if x == 0 and y == 0 and z == 0 then
        return base
      end
      return rexpr (base + {x,y,z}) %
        rect3d{
          lo = int3d{ x = 0,           y = 0,           z = 0           },
          hi = int3d{ x = [dims[1]-1], y = [dims[2]-1], z = [dims[3]-1] } }
      end
    else assert(false) end
  end
  -- Assertion
  -- self.params[1] : AST.Expression
  if self.func == L.assert then
    return rexpr
      RG.assert([self.params[1]:toRExpr(ctxt)], '(Liszt assertion)')
    end
  end
  -- Key unboxing
  -- self.params[1] : AST.Expression
  if self.func == L.id then
    return self.params[1]:toRExpr(ctxt)
  elseif self.func == L.xid then
    return rexpr [self.params[1]:toRExpr(ctxt)].x end
  elseif self.func == L.yid then
    return rexpr [self.params[1]:toRExpr(ctxt)].y end
  elseif self.func == L.zid then
    return rexpr [self.params[1]:toRExpr(ctxt)].z end
  end
  -- Unary arithmetic function
  -- self.params[1] : AST.Expression
  if UNARY_ARITH_FUNS[self.func] then
    local arg = self.params[1]:toRExpr(ctxt)
    return rexpr [UNARY_ARITH_FUNS[self.func]](arg) end
  end
  -- Binary arithmetic function
  -- self.params[1] : AST.Expression
  -- self.params[2] : AST.Expression
  if BINARY_ARITH_FUNS[self.func] then
    local arg1 = self.params[1]:toRExpr(ctxt)
    local arg2 = self.params[2]:toRExpr(ctxt)
    return rexpr [BINARY_ARITH_FUNS[self.func]](arg1, arg2) end
  end
  -- Min/max call
  -- self.params[1] : AST.Expression
  -- self.params[2] : AST.Expression
  if self.func == L.fmax or self.func == L.imax then
    local arg1 = self.params[1]:toRExpr(ctxt)
    local arg2 = self.params[2]:toRExpr(ctxt)
    return rexpr max(arg1, arg2) end
  end
  if self.func == L.fmin or self.func == L.imin then
    local arg1 = self.params[1]:toRExpr(ctxt)
    local arg2 = self.params[2]:toRExpr(ctxt)
    return rexpr min(arg1, arg2) end
  end
  -- Random number generator
  if self.func == L.rand then
    return rexpr [double](C.rand()) / C.RAND_MAX end
  end
  -- Dot product
  -- self.params[1] : AST.Expression
  -- self.params[2] : AST.Expression
  if self.func == L.dot then
    local t1 = self.params[1].node_type
    local t2 = self.params[2].node_type
    assert(t1:isvector() and t2:isvector() and t1.N == t2.N)
    local fun = emitDotProduct(toRType(t1.type), t1.N)
    local arg1 = self.params[1]:toRExpr(ctxt)
    local arg2 = self.params[2]:toRExpr(ctxt)
    return rexpr fun([arg1], [arg2]) end
  end
  -- Element-wise multiplication
  -- self.params[1] : AST.Expression
  -- self.params[2] : AST.Expression
  if self.func == L.times then
    local t1 = self.params[1].node_type
    local t2 = self.params[2].node_type
    assert(t1:isvector() and t2:isvector() and t1.N == t2.N)
    local fun = emitVectorVectorOp('*', toRType(t1.type), t1.N)
    local arg1 = self.params[1]:toRExpr(ctxt)
    local arg2 = self.params[2]:toRExpr(ctxt)
    return rexpr fun([arg1], [arg2]) end
  end
  -- Derive key value from indices
  -- self.params[1] : AST.VectorLiteral
  -- self.params[2] : AST.LuaObject
  --   .node_type.value : R.Relation
  -- TODO: Only allowing literals given directly
  if self.func == L.UNSAFE_ROW then
    local rel = self.params[2].node_type.value
    local keyExpr = self.params[1]:toRExpr(ctxt)
    local vec2idx = rel:emitVectorToIndexType()
    return rexpr vec2idx(keyExpr) end
  end
  -- Call to terra function
  -- self.params : AST.Expression*
  if self.func.is_a_terra_func then
    local args = newlist()
    for idx = 1, #self.params do
      args:insert(self.params[idx]:toRExpr(ctxt))
    end
    return rexpr [self.func.terrafn]([args]) end
  end
  -- Print statement
  -- self.params : AST.Expression*
  if self.func == L.print then
    local args = newlist()
    for idx = 1, #self.params do
      local arg = self.params[idx]:toRExpr(ctxt)
      if not self.params[idx].node_type:isvector() then
        args:insert(arg)
      else
        args:insert(rexpr [arg][0] end)
        args:insert(rexpr [arg][1] end)
        args:insert(rexpr [arg][2] end)
      end
    end
    local fmt = ""
    for idx = 1, #self.params do
      local ty = self.params[idx].node_type
      if not ty:isvector() then
        if ty == L.uint64 then
          fmt = fmt .. "%lu "
        elseif ty == L.int then
          fmt = fmt .. "%d "
        else
          fmt = fmt .. "%f "
        end
      else
        local val_fmt
        if ty.type == L.uint64 then
          val_fmt = "%lu"
        elseif ty == L.int then
          fmt = fmt .. "%d"
        else
          val_fmt = "%f"
        end
        fmt = fmt .. "("
        for idx = 1, ty.N do
          fmt = fmt .. val_fmt
          if idx ~= ty.N then
            fmt = fmt .. ", "
          end
        end
        fmt = fmt .. ") "
      end
    end
    fmt = fmt .. "\n"
    return rexpr C.printf([fmt], [args]) end
  end
  -- TODO: Not covered: L.cross, L.length
  assert(false)
end
function AST.Cast:toRExpr(ctxt)
  -- self.node_type : T.Type
  -- self.value     : AST.Expression
  return rexpr [toRType(self.node_type)]([self.value:toRExpr(ctxt)]) end
end
function AST.FieldAccess:toRExpr(ctxt)
  -- self.field : R.Field
  -- self.key   : AST.Expression
  local rel = self.key.node_type.relation
  -- TODO: Assuming that off-center accesses are only made using Affine
  -- expressions, therefore we don't need to bounds-check here.
  return rexpr
    [ctxt.relMap[rel]][ [self.key:toRExpr(ctxt)] ].[self.field:Name()]
  end
end
function AST.FieldAccessIndex:toRExpr(ctxt)
  -- self.base  : AST.FieldAccess
  -- self.field : R.Field
  -- self.key   : AST.Expression
  -- self.index : AST.Expression
  return emitIndexExpr(self.base:toRExpr(ctxt), self.index)
end
function AST.Global:toRExpr(ctxt)
  -- self.global : L.Global
  return rexpr
    [ctxt.globalMap[self.global]]
  end
end
function AST.GlobalIndex:toRExpr(ctxt)
  -- self.index  : AST.Expression
  -- self.global : L.Global
  return emitIndexExpr(ctxt.globalMap[self.global], self.index)
end
function AST.LetExpr:toRExpr(ctxt)
  -- self.block       : AST.Block
  -- self.exp         : AST.Expression
  -- self.orig_func   : F.Function?
  -- self.orig_params : (AST.Expression*)?
  assert(self.block:is(AST.Block))
  -- Call to user-defined helper function: emit as separate task
  if self.orig_func then
    return recoverHelperCall(self, ctxt)
  end
  -- Call to macro: handle common case of simple alias expression
  assert(#self.block.statements == 1)
  local decl = self.block.statements[1]
  assert(decl:is(AST.DeclStatement))
  ctxt:addAlias(decl.name, decl.initializer:toRExpr(ctxt))
  return self.exp:toRExpr(ctxt)
end
function AST.LuaObject:toRExpr(ctxt)
  quit(self)
end
function AST.MatrixLiteral:toRExpr(ctxt)
  quit(self)
end
function AST.Name:toRExpr(ctxt)
  -- self.name : AST.Symbol
  return assert(ctxt.localMap[self.name])
end
function AST.Number:toRExpr(ctxt)
  -- self.node_type : T.Type
  -- self.value     : number
  return rexpr [toRType(self.node_type)]([self.value]) end
end
function AST.Quote:toRExpr(ctxt)
  -- self.code : AST.Expression
  return self.code:toRExpr(ctxt)
end
function AST.RecordLiteral:toRExpr(ctxt)
  quit(self)
end
function AST.Reduce:toRExpr(ctxt)
  quit(self)
end
function AST.SquareIndex:toRExpr(ctxt)
  -- self.node_type : T.Type
  -- self.base      : AST.Expression
  -- self.index     : AST.Expression
  return emitIndexExpr(self.base:toRExpr(ctxt), self.index)
end
function AST.String:toRExpr(ctxt)
  quit(self)
end
function AST.TableLookup:toRExpr(ctxt)
  quit(self)
end
function AST.UnaryOp:toRExpr(ctxt)
  -- self.exp : AST.Expression
  -- self.op  : string
  local t = self.exp.node_type
  local arg = self.exp:toRExpr(ctxt)
  if t:isvector() and self.op == '-' then
    local fun = emitVectorScalarOp('*', toRType(t.type), t.N)
    return rexpr fun(arg, -1) end
  end
  assert(t:isscalar())
  return
    (self.op == '-')   and rexpr -arg    end or
    (self.op == 'not') and rexpr not arg end or
    assert(false)
end
function AST.VectorLiteral:toRExpr(ctxt)
  -- self.node_type : T.Type
  -- self.elems     : AST.Expression*
  return emitVectorCtor(
    toRType(self.node_type.type),
    newlist(self.elems):map(function(e) return e:toRExpr(ctxt) end))
end
function AST.Where:toRExpr(ctxt)
  quit(self)
end

-- FunContext -> RG.rquote
function AST.Statement:toRQuote(ctxt)
  error('Abstract Method')
end
function AST.Assignment:toRQuote(ctxt)
  -- self.lvalue   : AST.Expression
  -- self.exp      : AST.Expression
  -- self.reduceop : string?
  local lval = self.lvalue:toRExpr(ctxt)
  local exp = self.exp:toRExpr(ctxt)
  if self.reduceop then
    return emitReduce(self.reduceop, self.exp.node_type, lval, exp)
  else
    return rquote lval = exp end
  end
end
function AST.Break:toRQuote(ctxt)
  quit(self)
end
function AST.DeclStatement:toRQuote(ctxt)
  -- self.name        : AST.Symbol
  -- self.node_type   : T.Type
  -- self.initializer : AST.Expression
  local rsym = ctxt:addLocal(self.name)
  return rquote
    var [rsym] = [self.initializer:toRExpr(ctxt)]
  end
end
function AST.DeleteStatement:toRQuote(ctxt)
  -- self.key : AST.Expression
  local rel = ctxt.relMap[ctxt.domainRel]
  return rquote
    [rel][ [self.key:toRExpr(ctxt)] ].__valid = false
  end
end
function AST.DoStatement:toRQuote(ctxt)
  -- self.body        : AST.Block
  -- self.orig_func   : F.Function?
  -- self.orig_params : (AST.Expression*)?
  return self.body:toRQuote(ctxt)
end
function AST.ExprStatement:toRQuote(ctxt)
  -- self.exp : AST.Expression | AST.DoStatement
  if self.exp:is(AST.DoStatement) then
    return self.exp:toRQuote(ctxt)
  end
  return rquote [self.exp:toRExpr(ctxt)] end
end
function AST.FieldWrite:toRQuote(ctxt)
  -- self.fieldaccess : AST.FieldAccess
  -- self.exp         : AST.Expression
  -- self.reduceop    : string?
  local lval = self.fieldaccess:toRExpr(ctxt)
  local exp = self.exp:toRExpr(ctxt)
  if self.reduceop then
    return emitReduce(self.reduceop, self.exp.node_type, lval, exp)
  else
    return rquote lval = exp end
  end
end
function AST.GenericFor:toRQuote(ctxt)
  quit(self)
end
function AST.GlobalReduce:toRQuote(ctxt)
  -- self.global   : AST.Global
  -- self.reduceop : string
  -- self.exp      : AST.Expression
  assert(self.global.global == ctxt.reducedGlobal)
  local lval = ctxt.globalReduceAcc
  local exp = self.exp:toRExpr(ctxt)
  return emitReduce(self.reduceop, self.exp.node_type, lval, exp)
end
function AST.IfStatement:toRQuote(ctxt)
  -- self.if_blocks  : AST.CondBlock*
  -- self.else_block : AST.Block
  local quot
  for i=#self.if_blocks,1,-1 do
    local cond = self.if_blocks[i].cond:toRExpr(ctxt)
    local body = self.if_blocks[i].body:toRQuote(ctxt)
    if quot then
      quot = rquote if [cond] then [body] else [quot] end end
    elseif self.else_block then
      local innerElse = self.else_block:toRQuote(ctxt)
      quot = rquote if [cond] then [body] else [innerElse] end end
    else
      quot = rquote if [cond] then [body] end end
    end
  end
  return quot
end
function AST.InsertStatement:toRQuote(ctxt)
  -- self.record   : AST.RecordLiteral
  --   .names      : string*
  --   .exprs      : AST.Expression
  -- self.relation.node_type.value : R.Relation
  local rg = ctxt.relMap[self.relation.node_type.value]
  local elem = RG.newsymbol(nil, 'elem')
  local fldWriteQuotes = newlist()
  for i,name in ipairs(self.record.names) do
    fldWriteQuotes:insert(rquote
      elem.[name] = [self.record.exprs[i]:toRExpr(ctxt)]
    end)
  end
  return rquote
    var inserted = false
    for [elem] in rg do
      if not elem.__valid then
        elem.__valid = true
        [fldWriteQuotes]
        inserted = true
        break
      end
    end
    RG.assert(inserted, 'Out of space')
  end
end
function AST.NumericFor:toRQuote(ctxt)
  -- self.name  : AST.Symbol
  -- self.lower : AST.Expression
  -- self.upper : AST.Expression
  -- self.body  : AST.Block
  local i = ctxt:addLocal(self.name)
  return rquote
    for [i] = [self.lower:toRExpr(ctxt)], [self.lower:toRExpr(ctxt)] do
      [self.body:toRQuote(ctxt)]
    end
  end
end
function AST.RepeatStatement:toRQuote(ctxt)
  quit(self)
end
function AST.WhileStatement:toRQuote(ctxt)
  quit(self)
end

-- FunContext -> RG.rquote
function AST.Block:toRQuote(ctxt)
  local stmtQuotes =
    newlist(self.statements):map(function(stmt) return stmt:toRQuote(ctxt) end)
  return rquote
    [stmtQuotes]
  end
end

-------------------------------------------------------------------------------
-- Relation dumping & loading
-------------------------------------------------------------------------------

if USE_HDF then

  local HDF5 = terralib.includec(HDF_HEADER)

  -- HACK: Hardcoding missing #define's
  HDF5.H5F_ACC_TRUNC = 2
  HDF5.H5P_DEFAULT = 0

  -- string* -> RG.task
  -- TODO: Not caching the generated tasks.
  function R.Relation:emitDump(flds)
    local flds = flds:copy()
    if self:isFlexible() then
      local autoPartFld = self:AutoPartitionField()
      assert(not autoPartFld or flds:find(autoPartFld:Name()))
      flds:insert('__valid')
    end
    local dims = self:Dims()
    local nDims = #dims
    local isType = self:indexSpaceType()
    local fs = self:fieldSpace()
    local terra create(filename : rawstring)
      var file = HDF5.H5Fcreate(filename, HDF5.H5F_ACC_TRUNC,
                                HDF5.H5P_DEFAULT, HDF5.H5P_DEFAULT)
      var sizes : HDF5.hsize_t[nDims]
      escape
        if #dims == 1 then
          emit quote
            sizes[0] = [dims[1]]
          end
        elseif #dims == 2 then
          emit quote
            sizes[0] = [dims[1]]
            sizes[1] = [dims[2]]
          end
        elseif #dims == 3 then
          emit quote
            sizes[0] = [dims[1]]
            sizes[1] = [dims[2]]
            sizes[2] = [dims[3]]
          end
        else assert(false) end
      end
      var dataSpace = HDF5.H5Screate_simple([#dims], sizes, [&uint64](0))
      escape
        local header = newlist() -- terralib.quote*
        local footer = newlist() -- terralib.quote*
        -- terralib.type -> terralib.quote
        local function toHType(T)
          -- TODO: Not supporting: pointers, vectors, non-primitive arrays
          if T:isprimitive() then
            return
              -- HACK: Hardcoding missing #define's
              (T == int)    and HDF5.H5T_STD_I32LE_g  or
              (T == int8)   and HDF5.H5T_STD_I8LE_g   or
              (T == int16)  and HDF5.H5T_STD_I16LE_g  or
              (T == int32)  and HDF5.H5T_STD_I32LE_g  or
              (T == int64)  and HDF5.H5T_STD_I64LE_g  or
              (T == uint)   and HDF5.H5T_STD_U32LE_g  or
              (T == uint8)  and HDF5.H5T_STD_U8LE_g   or
              (T == uint16) and HDF5.H5T_STD_U16LE_g  or
              (T == uint32) and HDF5.H5T_STD_U32LE_g  or
              (T == uint64) and HDF5.H5T_STD_U64LE_g  or
              (T == bool)   and HDF5.H5T_STD_U8LE_g   or
              (T == float)  and HDF5.H5T_IEEE_F32LE_g or
              (T == double) and HDF5.H5T_IEEE_F64LE_g or
              assert(false)
          elseif T:isarray() then
            local elemType = toHType(T.type)
            local arrayType = symbol(HDF5.hid_t, 'arrayType')
            header:insert(quote
              var dims : HDF5.hsize_t[1]
              dims[0] = T.N
              var [arrayType] = HDF5.H5Tarray_create2(elemType, 1, dims)
            end)
            footer:insert(quote
              HDF5.H5Tclose(arrayType)
            end)
            return arrayType
          else assert(false) end
        end
        -- terralib.struct, set(string), string -> ()
        local function emitFieldDecls(fs, whitelist, prefix)
           -- TODO: Only supporting pure structs, not fspaces
          assert(fs:isstruct())
          for _,fld in ipairs(fs.entries) do
            if whitelist and not whitelist[fld.field] then
            elseif fld.type:isstruct() then
              emitFieldDecls(fld.type, nil, prefix..fld.field..'.')
            else
              local hName = prefix..fld.field
              local hType = toHType(fld.type)
              local dataSet = symbol(HDF5.hid_t, 'dataSet')
              header:insert(quote
                var [dataSet] = HDF5.H5Dcreate2(
                  file, hName, hType, dataSpace,
                  HDF5.H5P_DEFAULT, HDF5.H5P_DEFAULT, HDF5.H5P_DEFAULT)
              end)
              footer:insert(quote
                HDF5.H5Dclose(dataSet)
              end)
            end
          end
        end
        emitFieldDecls(fs, flds:toSet(), '')
        emit quote [header] end
        emit quote [footer:reverse()] end
      end
      HDF5.H5Sclose(dataSpace)
      HDF5.H5Fclose(file)
    end
    local dump __demand(__inline) task dump(r : region(isType, fs),
                                            filename : rawstring)
    where
      reads(r.[flds])
    do
      create(filename)
      var s = region([self:emitISpaceInit()], fs)
      attach(hdf5, s.[flds], filename, RG.file_read_write)
      acquire(s.[flds])
      copy(r.[flds], s.[flds])
      release(s.[flds])
      detach(hdf5, s.[flds])
    end
    setFunName(create, self:Name()..'_hdf5create_'..flds:join('_'))
    setTaskName(dump, self:Name()..'_hdf5dump_'..flds:join('_'))
    if DEBUG then
      prettyPrintFun(create)
      prettyPrintTask(dump)
    end
    return dump
  end

  -- string* -> RG.task
  -- TODO: Not caching the generated tasks.
  function R.Relation:emitLoad(flds)
    local flds = flds:copy()
    if self:isFlexible() then
      local autoPartFld = self:AutoPartitionField()
      assert(not autoPartFld or flds:find(autoPartFld:Name()))
      flds:insert('__valid')
    end
    local isType = self:indexSpaceType()
    local fs = self:fieldSpace()
    local load __demand(__inline) task load(r : region(isType, fs),
                                            filename : rawstring)
    where
      reads writes(r.[flds])
    do
      var s = region([self:emitISpaceInit()], fs)
      attach(hdf5, s.[flds], filename, RG.file_read_only)
      acquire(s.[flds])
      copy(s.[flds], r.[flds])
      release(s.[flds])
      detach(hdf5, s.[flds])
    end
    setTaskName(load, self:Name()..'_hdf5load_'..flds:join('_'))
    if DEBUG then prettyPrintTask(load) end
    return load
  end

end -- if USE_HDF

-------------------------------------------------------------------------------
-- Control program translation
-------------------------------------------------------------------------------

-- ProgramContext -> RG.rquote
function M.AST.Stmt:toRQuote(ctxt)
  error('Abstract method')
end
function M.AST.Block:toRQuote(ctxt)
  return rquote
    [self.stmts:map(function(s) return s:toRQuote(ctxt) end)]
  end
end
function M.AST.ForEach:toRQuote(ctxt)
  -- Translate kernel to task
  local info = self.fun:_get_typechecked(42, self.rel, {})
  local tsk, fCtxt = self.fun:toKernelTask()
  -- Collect arguments for call
  local actualArgs = newlist()
  local c = RG.newsymbol(nil, 'c')
  if RG.config['parallelize'] and not (isEmpty(info.inserts) and isEmpty(info.deletes)) then
    -- HACK: Need to manually parallelize insertion kernels.
    assert(not self.subset)
    actualArgs:insert(rexpr [ctxt.primPart[self.rel]][c] end)
    for _,rel in ipairs(fCtxt.accessedRels) do
      actualArgs:insert(rexpr [ctxt.primPart[rel]][c] end)
    end
  else
    actualArgs:insert(self.subset and ctxt.subsetMap[self.subset]
                      or ctxt.relMap[self.rel])
    for _,rel in ipairs(fCtxt.accessedRels) do
      actualArgs:insert(ctxt.relMap[rel])
    end
  end
  for _,g in ipairs(fCtxt.readGlobals) do
    actualArgs:insert(assert(ctxt.globalMap[g]))
  end
  -- Synthesize call expression
  local callExpr = rexpr [tsk]([actualArgs]) end
  local callQuote = rquote [callExpr] end
  if fCtxt.reducedGlobal then
    local retSym = ctxt.globalMap[fCtxt.reducedGlobal]
    local op = fCtxt.globalReduceOp
    callQuote =
      (op == '+')   and rquote [retSym] +=   [callExpr]     end or
      (op == '-')   and rquote [retSym] +=   [callExpr]     end or
      (op == '*')   and rquote [retSym] *=   [callExpr]     end or
      (op == '/')   and rquote [retSym] *=   [callExpr]     end or
      (op == 'max') and rquote [retSym] max= [callExpr]     end or
      (op == 'min') and rquote [retSym] min= [callExpr]     end or
      assert(false)
  end
  if RG.config['parallelize'] and not (isEmpty(info.inserts) and isEmpty(info.deletes)) then
    -- HACK: Need to manually parallelize insertion kernels.
    callQuote = rquote
      for [c] in [ctxt.primColors] do
        [callQuote]
      end
    end
  end
  -- Update primary partitioning (if appropriate)
  local primPartQuote = rquote end
  if RG.config['parallelize'] then
    local pt = info.field_use[self.rel:AutoPartitionField()]
    if pt and pt.write then
      primPartQuote = self.rel:emitPrimPartUpdate(ctxt)
    end
  end
  return rquote
    [callQuote];
    [primPartQuote]
  end
end
function M.AST.If:toRQuote(ctxt)
  if self.elseBlock then
    return rquote
      var thenFlag = [int]([self.cond:toRExpr(ctxt)])
      var elseFlag = 1 - thenFlag
      while thenFlag > 0 do
        [self.thenBlock:toRQuote(ctxt)]
        thenFlag -= 1
      end
      while elseFlag > 0 do
        [self.elseBlock:toRQuote(ctxt)]
        elseFlag -= 1
      end
    end
  else
    return rquote
      var flag = [int]([self.cond:toRExpr(ctxt)])
      while flag > 0 do
        [self.thenBlock:toRQuote(ctxt)]
        flag -= 1
      end
    end
  end
end
function M.AST.FillField:toRQuote(ctxt)
  error('Fill operations are handled separately')
end
function M.AST.SetGlobal:toRQuote(ctxt)
  return rquote
    [ctxt.globalMap[self.global]] = [self.expr:toRExpr(ctxt)]
  end
end
function M.AST.While:toRQuote(ctxt)
  if self.spmd then
    return rquote
      __demand(__spmd)
      while [self.cond:toRExpr(ctxt)] do
        [self.body:toRQuote(ctxt)]
      end
    end
  else
    return rquote
      while [self.cond:toRExpr(ctxt)] do
        [self.body:toRQuote(ctxt)]
      end
    end
  end
end
function M.AST.Print:toRQuote(ctxt)
  local valRExprs = self.vals:map(function(v) return v:toRExpr(ctxt) end)
  return rquote
    C.printf([self.fmt], valRExprs)
  end
end
function M.AST.Dump:toRQuote(ctxt)
  local dump = self.rel:emitDump(self.flds)
  local relSym = ctxt.relMap[self.rel]
  local valRExprs = self.vals:map(function(v) return v:toRExpr(ctxt) end)
  return rquote
    var filename = [rawstring](C.malloc(256))
    C.snprintf(filename, 256, [self.file], valRExprs)
    dump(relSym, filename)
    C.free(filename)
  end
end
function M.AST.Load:toRQuote(ctxt)
  local load = self.rel:emitLoad(self.flds)
  local relSym = ctxt.relMap[self.rel]
  local valRExprs = self.vals:map(function(v) return v:toRExpr(ctxt) end)
  local primPartQuote = rquote end
  if RG.config['parallelize'] then
    if self.flds:find(self.rel:AutoPartitionField()) then
      if self:isFlexible() then
        primPartQuote = self.rel:emitPrimPartCheck(ctxt)
      else
        primPartQuote = self.rel:emitPrimPartUpdate(ctxt)
      end
    end
  end
  return rquote
    var filename = [rawstring](C.malloc(256))
    C.snprintf(filename, 256, [self.file], valRExprs)
    load(relSym, filename)
    C.free(filename)
    [primPartQuote]
  end
end

-- ProgramContext -> RG.rexpr
function M.AST.Cond:toRExpr(ctxt)
  error('Abstract method')
end
function M.AST.Literal:toRExpr(ctxt)
  return rexpr [self.val] end
end
function M.AST.And:toRExpr(ctxt)
  return rexpr [self.lhs:toRExpr(ctxt)] and [self.rhs:toRExpr(ctxt)] end
end
function M.AST.Or:toRExpr(ctxt)
  return rexpr [self.lhs:toRExpr(ctxt)] or [self.rhs:toRExpr(ctxt)] end
end
function M.AST.Not:toRExpr(ctxt)
  return rexpr not [self.cond:toRExpr(ctxt)] end
end
function M.AST.Compare:toRExpr(ctxt)
  local a = self.lhs:toRExpr(ctxt)
  local b = self.rhs:toRExpr(ctxt)
  return
    (self.op == '==') and rexpr a == b end or
    (self.op == '~=') and rexpr a ~= b end or
    (self.op == '>')  and rexpr a > b  end or
    (self.op == '<')  and rexpr a < b  end or
    (self.op == '>=') and rexpr a >= b end or
    (self.op == '<=') and rexpr a <= b end or
    assert(false)
end

-- ProgramContext -> RG.rexpr
function M.AST.Expr:toRExpr(ctxt)
  error('Abstract method')
end
function M.AST.Const:toRExpr(ctxt)
  return rexpr [toRConst(self.val)] end
end
function M.AST.GetGlobal:toRExpr(ctxt)
  local globSym = assert(ctxt.globalMap[self.global])
  return rexpr globSym end
end
function M.AST.BinaryOp:toRExpr(ctxt)
  local a = self.lhs:toRExpr(ctxt)
  local b = self.rhs:toRExpr(ctxt)
  return
    (self.op == '+') and rexpr a + b end or
    (self.op == '-') and rexpr a - b end or
    (self.op == '*') and rexpr a * b end or
    (self.op == '/') and rexpr a / b end or
    (self.op == '%') and rexpr a % b end or
    assert(false)
end
function M.AST.UnaryOp:toRExpr(ctxt)
  local a = self.arg:toRExpr(ctxt)
  return
    (self.op == '-') and rexpr -a end or
    assert(false)
end

-- ProgramContext, M.AST.FillField -> RG.rquote*
local function emitFillTaskCalls(ctxt, fillStmts)
  local fillsPerRelation = {} -- map(R.Relation,M.AST.FillField)
  local mustUpdatePrimPart = {} -- set(R.Relation)
  for _,fill in ipairs(fillStmts) do
    local rel = fill.fld:Relation()
    local stmts = fillsPerRelation[rel] or newlist()
    stmts:insert(fill)
    fillsPerRelation[rel] = stmts
    if RG.config['parallelize'] then
      if fill.fld == rel:AutoPartitionField() then
        assert(not rel:isFlexible())
        mustUpdatePrimPart[rel] = true
      end
    end
  end
  local fillTasks = {} -- map(R.Relation,RG.task)
  for rel,fills in pairs(fillsPerRelation) do
    local arg = RG.newsymbol(rel:regionType(), rel:Name())
    local privileges = newlist()
    privileges:insert(RG.privilege(RG.reads, arg))
    privileges:insert(RG.privilege(RG.writes, arg))
    local tsk
    if RG.check_cuda_available() then
      __demand(__parallel, __cuda)
      task tsk([arg]) where [privileges] do
        [fills:map(function(fill) return rquote
           for e in arg do
             e.[fill.fld:Name()] = [toRConst(fill.val, fill.fld:Type())]
           end
         end end)]
      end
    else
      __demand(__parallel)
      task tsk([arg]) where [privileges] do
        [fills:map(function(fill) return rquote
           for e in arg do
             e.[fill.fld:Name()] = [toRConst(fill.val, fill.fld:Type())]
           end
         end end)]
      end
    end
    fillTasks[rel] = tsk
    setTaskName(tsk, rel:Name()..'_fillTask')
    if DEBUG then prettyPrintTask(tsk) end
  end
  local calls = newlist() -- RG.rquote*
  for rel,tsk in pairs(fillTasks) do
    calls:insert(rquote [tsk]([ctxt.relMap[rel]]) end)
    if mustUpdatePrimPart[rel] then
      calls:insert(rel:emitPrimPartUpdate(ctxt))
    end
  end
  return calls
end

-- (()->())?, (string*)? -> ()
function A.translateAndRun(mapper_registration, link_flags)
  if DEBUG then print('import "regent"') end
  local header = newlist() -- RG.rquote*
  local body = newlist() -- RG.rquote*
  local ctxt = { -- ProgramContext
    globalMap  = {},  -- map(L.Global, RG.symbol)
    relMap     = {},  -- map(R.Relation, RG.symbol)
    subsetMap  = {},  -- map(R.Subset, RG.symbol)
    primPart   = {},  -- map(R.Relation, RG.symbol)
    queueMap   = {},  -- map(R.Relation, RG.symbol)
    qSrcPart   = {},  -- map(R.Relation, RG.symbol)
    qDstPart   = {},  -- map(R.Relation, RG.symbol)
    primColors = nil, -- RG.symbol
  }
  -- Collect declarations
  local globalInits = {} -- map(L.Global, M.ExprConst)
  local rels = newlist() -- R.Relation*
  for _,decl in ipairs(M.decls()) do
    if M.AST.NewField.check(decl) then
      -- Do nothing
    elseif M.AST.NewFunction.check(decl) then
      -- Do nothing
    elseif M.AST.NewGlobal.check(decl) then
      globalInits[decl.global] = decl.init
    elseif M.AST.NewRelation.check(decl) then
      rels:insert(decl.rel)
    elseif M.AST.NewDivision.check(decl) then
      -- Do nothing
    else assert(false) end
  end
  -- Emit global declarations
  for g,val in pairs(globalInits) do
    local x = RG.newsymbol(toRType(g:Type()), idSanitize(g:Name()))
    ctxt.globalMap[g] = x
    header:insert(rquote var [x] = [toRConst(val, g:Type())] end)
  end
  -- Emit region declarations and user-defined divisions
  for _,rel in ipairs(rels) do
    local rg = RG.newsymbol(nil, rel:Name())
    ctxt.relMap[rel] = rg
    header:insert(rel:emitRegionInit(rg))
    for _,div in ipairs(rel:Divisions()) do
      local colors = RG.newsymbol(nil, 'colors')
      local coloring = RG.newsymbol(nil, 'coloring')
      header:insert(rquote
        var [colors] = ispace(int1d, [#div])
        var [coloring] = RG.c.legion_domain_point_coloring_create()
      end)
      for i,subset in ipairs(div) do
        local rect = subset:Rectangle() -- int[1-3][2]
        local rectExpr =
          (#rect == 1) and rexpr
            rect1d{ lo = [rect[1][1]], hi = [rect[1][2]] }
          end or
          (#rect == 2) and rexpr
            rect2d{
              lo = int2d{ x = [rect[1][1]], y = [rect[2][1]] },
              hi = int2d{ x = [rect[1][2]], y = [rect[2][2]] }}
          end or
          (#rect == 3) and rexpr
            rect3d{
              lo = int3d{ x = [rect[1][1]], y = [rect[2][1]], z = [rect[3][1]] },
              hi = int3d{ x = [rect[1][2]], y = [rect[2][2]], z = [rect[3][2]] }}
          end or
          assert(false)
        header:insert(rquote
          RG.c.legion_domain_point_coloring_color_domain
            (coloring, int1d(i-1), rectExpr)
        end)
      end
      local p = RG.newsymbol(nil, 'p')
      header:insert(rquote
        var [p] = partition(disjoint, rg, coloring, colors)
      end)
      for i,subset in ipairs(div) do
        local subrg = RG.newsymbol(nil, idSanitize(subset:FullName()))
        ctxt.subsetMap[subset] = subrg
        header:insert(rquote
          var [subrg] = p[i-1]
        end)
      end
      header:insert(rquote
        RG.c.legion_domain_point_coloring_destroy(coloring)
      end)
    end
  end
  -- Emit primary partitioning scheme
  if RG.config['parallelize'] then
    ctxt.primColors = RG.newsymbol(nil, 'primColors')
    header:insert(rquote
      var [ctxt.primColors] = ispace(int3d, {NX,NY,NZ})
    end)
    for _,rel in ipairs(rels) do
      local rg = ctxt.relMap[rel]
      local p = RG.newsymbol(nil, rel:Name()..'_primPart')
      ctxt.primPart[rel] = p
      header:insert(rel:emitPrimPartInit(rg, p, ctxt.primColors))
      -- Emit transfer queues for flexible relations with an auto-partitioning
      -- constraint.
      if rel:isFlexible() and rel:AutoPartitionField() then
        local q = RG.newsymbol(nil, rel:Name()..'_queue')
        ctxt.queueMap[rel] = q
        local qpsrc = RG.newsymbol(nil, rel:Name()..'_qSrcPart')
        ctxt.qSrcPart[rel] = qpsrc
        local qpdst = RG.newsymbol(nil, rel:Name()..'_qDstPart')
        ctxt.qDstPart[rel] = qpdst
        header:insert(rel:emitQueueInit(q))
        header:insert(rel:emitQueuePartInit(q, qpsrc, qpdst, ctxt.primColors))
      end
    end
  end
  -- Process fill statements
  local fillStmts = newlist()
  for _,s in ipairs(M.stmts()) do
    if M.AST.FillField.check(s) then
      fillStmts:insert(s)
    end
  end
  body:insertall(emitFillTaskCalls(ctxt, fillStmts))
  -- Process other statements
  for _,s in ipairs(M.stmts()) do
    if not M.AST.FillField.check(s) then
      body:insert(s:toRQuote(ctxt))
    end
  end
  -- Synthesize main task
  local main
  if RG.config['parallelize'] then
    local opts = newlist() -- RG.rexpr*
    opts:insertall(rels:map(function(rel) return ctxt.primPart[rel] end))
    opts:insert(rexpr [ctxt.primColors] end)
    for _,domRel in ipairs(rels) do
      local autoPartFld = domRel:AutoPartitionField()
      if domRel:isFlexible() and autoPartFld then
        local rngRel = autoPartFld:Type().relation
        local domRg = ctxt.relMap[domRel]
        local domPart = ctxt.primPart[domRel]
        local rngRg = ctxt.relMap[rngRel]
        local rngPart = ctxt.primPart[rngRel]
        opts:insert(rexpr
          image(rngRg, domPart, domRg.[autoPartFld:Name()]) <= rngPart
        end)
      end
    end
    task main()
      [header]
      __parallelize_with [opts] do [body] end
    end
  else
    task main()
      [header];
      [body]
    end
  end
  setTaskName(main, 'main')
  if DEBUG then
    prettyPrintTask(main)
    print('regentlib.start('..main:getname()[1]..')')
  end
  -- Emit to executable or run
  if SAVEOBJ then
    print('Saving executable to '..OBJNAME)
    link_flags = link_flags or newlist()
    for idx = 1, #LIBS do
      link_flags[#link_flags + 1] = LIBS[idx]
    end
    RG.saveobj(main, OBJNAME, 'executable', mapper_registration, link_flags)
  else
    RG.start(main, mapper_registration)
  end
end
