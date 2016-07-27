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
local LOG = require 'ebb.src.api_log'
local P   = require 'ebb.src.phase'
local R   = require 'ebb.src.relations'
local RG  = regentlib
local T   = require 'ebb.src.types'

local DEBUG = true

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
local function minValue(typ)
  return
    (typ == int)    and -2147483648 or
    (typ == int8)   and -128 or
    (typ == int16)  and -32768 or
    (typ == int32)  and -2147483648 or
    (typ == int64)  and -9223372036854775808 or
    (typ == uint)   and 0 or
    (typ == uint8)  and 0 or
    (typ == uint16) and 0 or
    (typ == uint32) and 0 or
    (typ == uint64) and 0 or
    (typ == bool)   and 0 or
    (typ == float)  and -math.huge or
    (typ == double) and -math.huge or
    assert(false)
end

-- terralib.type -> number
local function maxValue(typ)
  return
    (typ == int)    and 2147483647 or
    (typ == int8)   and 127 or
    (typ == int16)  and 32767 or
    (typ == int32)  and 2147483647 or
    (typ == int64)  and 9223372036854775807 or
    (typ == uint)   and 4294967295 or
    (typ == uint8)  and 255 or
    (typ == uint16) and 65535 or
    (typ == uint32) and 4294967295 or
    (typ == uint64) and 18446744073709551615 or
    (typ == bool)   and 1 or
    (typ == float)  and math.huge or
    (typ == double) and math.huge or
    assert(false)
end

-- string, terralib.type -> number
local function opIdentity(op, typ)
  return
    (op == '+')   and 0 or
    (op == '-')   and 0 or
    (op == '*')   and 1 or
    (op == '/')   and 1 or
    (op == 'max') and minValue(typ) or
    (op == 'min') and minValue(typ) or
    assert(false)
end

-------------------------------------------------------------------------------
-- Basic Regent mappings
-------------------------------------------------------------------------------

-- map(B.Builtin, (double -> double))
local unaryArithFuns = {
  [L.acos]  = C.acos,
  [L.asin]  = C.asin,
  [L.atan]  = C.atan,
  [L.cbrt]  = C.cbrt,
  [L.ceil]  = C.ceil,
  [L.cos]   = C.cos,
  [L.fabs]  = C.fabs,
  [L.floor] = C.floor,
  [L.fmod]  = C.fmod,
  [L.log]   = C.log,
  [L.pow]   = C.pow,
  [L.sin]   = C.sin,
  [L.sqrt]  = C.sqrt,
  [L.tan]   = C.tan,
}

-- map(B.Builtin, (double, double -> double))
local binaryArithFuns = {
  [L.fmax]  = C.fmax,
  [L.fmin]  = C.fmin,
}

-- T.Type -> terralib.type
local function toRType(ltype)
  if ltype:isprimitive() then
    return ltype:terratype()
  elseif ltype:isvector() then
    return toRType(ltype.type)[ltype.N]
  elseif ltype:ismatrix() then
    return toRType(ltype.type)[ltype.Nrow][ltype.Ncol]
  else assert(false) end
end

-- Literal = boolean | number | Literal[N]
-- terralib.type, Literal -> RG.rexpr
local function toRLiteral(typ, lit)
  if type(lit) == 'boolean' then
    assert(typ == boolean)
    return rexpr lit end
  elseif type(lit) == 'number' then
    return rexpr [typ](lit) end
  elseif type(lit) == 'table' then
    assert(terralib.israwlist(lit))
    assert(#lit == typ.N)
    if #lit == 1 then
      local a = toRLiteral(typ.type, lit[1])
      return rexpr array(a) end
    elseif #lit == 2 then
      local a = toRLiteral(typ.type, lit[1])
      local b = toRLiteral(typ.type, lit[2])
      return rexpr array(a, b) end
    elseif #lit == 3 then
      local a = toRLiteral(typ.type, lit[1])
      local b = toRLiteral(typ.type, lit[2])
      local c = toRLiteral(typ.type, lit[3])
      return rexpr array(a, b, c) end
    else assert(false) end
  else assert(false) end
end

-------------------------------------------------------------------------------
-- Relation-to-region translation
-------------------------------------------------------------------------------

-- () -> RG.ispace_type
function R.Relation:indexSpaceType()
  local dims = self:Dims()
  return
    (#dims == 1) and ispace(int1d) or
    (#dims == 2) and ispace(int2d) or
    (#dims == 3) and ispace(int3d) or
    assert(false)
end

-- () -> terralib.struct
R.Relation.fieldSpace = terralib.memoize(function(self)
  local fs = terralib.types.newstruct(self:Name() .. '_columns')
  for _,fld in ipairs(self._fields) do
    fs.entries:insert({fld:Name(), toRType(fld:Type())})
  end
  if DEBUG then fs:printpretty() end
  return fs
end)

-- () -> RG.region_type
function R.Relation:regionType()
  -- Region types in signatures must be distinct, so we're not caching here.
  return region(self:indexSpaceType(), self:fieldSpace())
end

-- () -> RG.rexpr
function R.Relation:mkISpaceInit()
  local dims = self:Dims()
  return
    (#dims == 1) and rexpr
      ispace(int1d, dims[1])
    end or
    (#dims == 2) and rexpr
      ispace(int2d, { x = [dims[1]], y = [dims[2]] })
    end or
    (#dims == 3) and rexpr
      ispace(int3d, { x = [dims[1]], y = [dims[2]], z = [dims[3]] })
    end or
    assert(false)
end

-- () -> RG.rexpr
function R.Relation:mkRegionInit()
  local ispaceExpr = self:mkISpaceInit()
  local fspaceExpr = self:fieldSpace()
  return rexpr region(ispaceExpr, fspaceExpr) end
end

-------------------------------------------------------------------------------
-- Kernel AST translation
-------------------------------------------------------------------------------

local Context = {}
Context.__index = Context

-- R.Relation, AST.Symbol -> Context
function Context.New(rel, argLSym)
  local dom = RG.newsymbol(rel:regionType(), 'dom')
  local univ = RG.newsymbol(rel:regionType(), rel:Name())
  return setmetatable({
    localMap        = {},                 -- map(AST.Symbol, RG.symbol)
    globalMap       = {},                 -- map(L.Global, RG.symbol)
    relation        = rel,                -- R.Relation
    domain          = dom,                -- RG.symbol
    universe        = univ,               -- RG.symbol
    readGlobals     = terralib.newlist(), -- L.Global*
    reducedGlobal   = nil,                -- L.Global
    globalReduceAcc = nil,                -- RG.symbol
    globalReduceOp  = nil,                -- string
  }, Context)
end

-- AST.Symbol -> RG.symbol
function Context:addLocal(lsym)
  assert(not self.localMap[lsym])
  local rsym = RG.newsymbol(tostring(lsym))
  self.localMap[lsym] = rsym
  return rsym
end

-- L.Global -> RG.symbol
function Context:addGlobalRead(glob)
  assert(not self.globalMap[glob])
  local rsym = RG.newsymbol(toRType(glob:Type()))
  self.globalMap[glob] = rsym
  self.readGlobals:insert(glob)
  return rsym
end

-- L.Global, string -> ()
function Context:addGlobalReduce(glob, op)
  assert(not self.reducedGlobal)
  self.reducedGlobal = glob
  self.globalReduceAcc = RG.newsymbol(toRType(glob:Type()), 'acc')
  self.globalReduceOp = op
end

-- () -> RG.symbol*
function Context:globalArgs()
  return self.readGlobals:map(function(g) return self.globalMap[g] end)
end

-- FunInfo = {
--   name           : string
--   relation       : R.Relation
--   field_use      : map(R.Field, P.PhaseType)
--   field_accesses : map(R.Field, S.AccessPattern)
--   global_use     : map(L.Global, P.PhaseType)
-- }

-- FunInfo -> RG.task, Context
function AST.UserFunction:toTask(info)
  -- self.params : AST.Symbol*
  -- self.body   : AST.Block
  assert(not self.exp)
  local ctxt = Context.New(info.relation, self.params[1])
  local dom = ctxt.domain
  local univ = ctxt.universe
  local loopVar = ctxt:addLocal(self.params[1])
  -- Process field access modes
  local readCols    = terralib.newlist()
  local writeCols   = terralib.newlist()
  local plusRdCols  = terralib.newlist()
  local minusRdCols = terralib.newlist()
  local multRdCols  = terralib.newlist()
  local divRdCols   = terralib.newlist()
  local maxRdCols   = terralib.newlist()
  local minRdCols   = terralib.newlist()
  for fld,pt in pairs(info.field_use) do
    assert(fld:Relation() == info.relation)
    -- Assuming phase checking has checked for errors
    if pt.read then readCols:insert(fld:Name()) end
    if pt.write then writeCols:insert(fld:Name()) end
    if pt.reduceop then
      local rdCols =
        (pt.reduceop == '+')   and plusRdCols or
        (pt.reduceop == '-')   and minusRdCols or
        (pt.reduceop == '*')   and multRdCols or
        (pt.reduceop == '/')   and divRdCols or
        (pt.reduceop == 'max') and maxRdCols or
        (pt.reduceop == 'min') and minRdCols or
        assert(false)
      rdCols:insert(fld:Name())
    end
  end
  -- Process global access modes
  for g,pt in pairs(info.global_use) do
    if pt.read and not pt.reduceop then
      ctxt:addGlobalRead(g)
    elseif pt.reduceop and not pt.read then
      ctxt:addGlobalReduce(g, pt.reduceop)
    else assert(false) end
  end
  -- Synthesize task
  local body = terralib.newlist()
  if ctxt.reducedGlobal then
    local accInitVal =
      opIdentity(ctxt.globalReduceOp, ctxt.globalReduceAcc:gettype())
    body:insert(rquote
      var [ctxt.globalReduceAcc] = [accInitVal]
    end)
  end
  body:insert(rquote
    for [loopVar] in dom do
      [self.body:toRQuote(ctxt)]
    end
  end)
  if ctxt.reducedGlobal then
    body:insert(rquote
      return [ctxt.globalReduceAcc]
    end)
  end
  local task tsk( [dom], [univ], [ctxt:globalArgs()] ) where
    dom <= univ,
    reads      (univ.[readCols]),
    writes     (univ.[writeCols]),
    reduces +  (univ.[plusRdCols]),
    reduces -  (univ.[minusRdCols]),
    reduces *  (univ.[multRdCols]),
    reduces /  (univ.[divRdCols]),
    reduces max(univ.[maxRdCols]),
    reduces min(univ.[minRdCols])
  do
    [body]
  end
  tsk:setname(info.name)
  tsk.ast.name[1] = info.name -- XXX: Dangerous
  -- TODO: Pass global-use information to the caller.
  if DEBUG then tsk:printpretty() end
  return tsk, ctxt
end

-- Context -> RG.rexpr
function AST.Expression:toRExpr(ctxt)
  error('Abstract Method')
end
function AST.BinaryOp:toRExpr(ctxt)
  -- self.lhs : AST.Expression
  -- self.rhs : AST.Expression
  -- self.op  : string
  local a = self.lhs:toRExpr(ctxt)
  local b = self.rhs:toRExpr(ctxt)
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
  quit(self)
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
    assert(rel == ctxt.relation)
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
      return rexpr (base + {x,y}) % [ctxt.universe].bounds end
    elseif N == 3 then
      local x = mat[1][4]
      local y = mat[2][4]
      local z = mat[3][4]
      return rexpr (base + {x,y,z}) % [ctxt.universe].bounds end
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
    -- TODO: Need to do something extra here?
    return self.params[1]:toRExpr(ctxt)
  elseif self.func == L.xid then
    return rexpr [ self.params[1]:toRExpr(ctxt) ].x end
  elseif self.func == L.yid then
    return rexpr [ self.params[1]:toRExpr(ctxt) ].y end
  elseif self.func == L.zid then
    return rexpr [ self.params[1]:toRExpr(ctxt) ].z end
  end
  -- Unary arithmetic function
  -- self.params[1] : AST.Expression
  if unaryArithFuns[self.func] then
    local arg = self.params[1]:toRExpr(ctxt)
    return rexpr [ unaryArithFuns[self.func] ](arg) end
  end
  -- Binary arithmetic function
  -- self.params[1] : AST.Expression
  -- self.params[2] : AST.Expression
  if binaryArithFuns[self.func] then
    local arg1 = self.params[1]:toRExpr(ctxt)
    local arg2 = self.params[2]:toRExpr(ctxt)
    return rexpr [ binaryArithFuns[self.func] ](arg1, arg2) end
  end
  -- TODO: Not covered:
  -- L.print L.rand
  -- L.dot L.cross L.length
  -- L.UNSAFE_ROW
  assert(false)
end
function AST.Cast:toRExpr(ctxt)
  -- self.node_type : T.Type
  -- self.value     : AST.Expression
  local rtype = toRType(self.node_type)
  return rexpr
    [rtype]([self.value:toRExpr(ctxt)])
  end
end
function AST.FieldAccess:toRExpr(ctxt)
  -- self.field : R.Field
  -- self.key   : AST.Expression
  -- TODO:
  -- * Verify it's actually a key on the argument relation.
  -- * Check for periodic boundaries here as well?
  return rexpr
    [ctxt.universe][ [self.key:toRExpr(ctxt)] ].[self.field:Name()]
  end
end
function AST.FieldAccessIndex:toRExpr(ctxt)
  -- TODO: Same checks as AST.FieldAccess
  quit(self)
end
function AST.Global:toRExpr(ctxt)
  quit(self)
end
function AST.GlobalIndex:toRExpr(ctxt)
  quit(self)
end
function AST.LetExpr:toRExpr(ctxt)
  quit(self)
end
function AST.LuaObject:toRExpr(ctxt)
  quit(self)
end
function AST.MatrixLiteral:toRExpr(ctxt)
  quit(self)
end
function AST.Name:toRExpr(ctxt)
  -- self.name : AST.Symbol
  return rexpr [ctxt.localMap[self.name]] end
end
function AST.Number:toRExpr(ctxt)
  -- self.value : number
  return rexpr [self.value] end
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
  quit(self)
end
function AST.String:toRExpr(ctxt)
  quit(self)
end
function AST.TableLookup:toRExpr(ctxt)
  quit(self)
end
function AST.UnaryOp:toRExpr(ctxt)
  quit(self)
end
function AST.VectorLiteral:toRExpr(ctxt)
  quit(self)
end
function AST.Where:toRExpr(ctxt)
  quit(self)
end

-- Context -> RG.rquote
function AST.Statement:toRQuote(ctxt)
  error('Abstract Method')
end
function AST.Assignment:toRQuote(ctxt)
  -- self.lvalue : AST.Expression
  -- self.exp    : AST.Expression
  return rquote
    [self.lvalue:toRExpr(ctxt)] = [self.exp:toRExpr(ctxt)]
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
  quit(self)
end
function AST.DoStatement:toRQuote(ctxt)
  quit(self)
end
function AST.ExprStatement:toRQuote(ctxt)
  -- self.exp : AST.Expression
  return rquote [self.exp:toRExpr(ctxt)] end
end
function AST.FieldWrite:toRQuote(ctxt)
  -- self.fieldaccess : AST.FieldAccess
  -- self.exp         : AST.Expression
  return rquote
    [self.fieldaccess:toRExpr(ctxt)] = [self.exp:toRExpr(ctxt)]
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
  local acc = ctxt.globalReduceAcc
  local val = self.exp:toRExpr(ctxt)
  return
    (self.reduceop == '+')   and rquote acc += val   end or
    (self.reduceop == '-')   and rquote acc -= val   end or
    (self.reduceop == '*')   and rquote acc *= val   end or
    (self.reduceop == '/')   and rquote acc /= val   end or
    (self.reduceop == 'max') and rquote acc max= val end or
    (self.reduceop == 'min') and rquote acc min= val end or
    assert(false)
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
  quit(self)
end
function AST.NumericFor:toRQuote(ctxt)
  quit(self)
end
function AST.RepeatStatement:toRQuote(ctxt)
  quit(self)
end
function AST.WhileStatement:toRQuote(ctxt)
  quit(self)
end

-- Context -> RG.rquote
function AST.Block:toRQuote(ctxt)
  local stmtQuotes =
    terralib.newlist(self.statements):map(function(stmt)
      return stmt:toRQuote(ctxt)
    end)
  return rquote
    [stmtQuotes]
  end
end

-- () -> RG.task, Context
function F.Function:toTask()
  local rawAST = self._decl_ast
  assert(#rawAST.params == 1)
  local argType = rawAST.ptypes[1]
  assert(argType:iskey())
  local argRel = argType.relation
  local info = self:_get_typechecked(42, argRel, {})
  -- info : {
  --   ...
  --   typed_ast      : AST.UserFunction
  --   field_use      : map(R.Field, P.PhaseType)
  --   field_accesses : map(R.Field, S.AccessPattern)
  --   global_use     : map(L.Global, P.PhaseType)
  -- }
  info.name = self._name
  info.relation = argRel
  return info.typed_ast:toTask(info)
end

-- () -> boolean
function F.Function:isKernel()
  return (#self._decl_ast.params == 1 and
          self._decl_ast.ptypes[1] and
          self._decl_ast.ptypes[1]:iskey())
end

-------------------------------------------------------------------------------
-- Control program translation
-------------------------------------------------------------------------------

function A.translateAndRun()
  local stmts = terralib.newlist()
  -- Collect declarations
  local globalInits = {} -- map(L.Global, Literal)
  local rels = terralib.newlist() -- R.Relation*
  local funs = terralib.newlist() -- F.Function*
  local subsetDefs = {} -- map(R.Subset, (int[1-3][2])*)
  for _,call in ipairs(LOG.log.entries) do
    if call.name == 'ForEachCall' then
      -- Do nothing
    elseif call.name == 'GetGlobal' then
      -- Do nothing
    elseif call.name == 'LoadField' then
      -- Do nothing
    elseif call.name == 'NewField' then
      -- Do nothing
    elseif call.name == 'NewFunction' then
      local f = call.return_val
      if f:isKernel() then
        funs:insert(f)
      end
    elseif call.name == 'NewGlobal' then
      globalInits[call.return_val] = call.args[2]
    elseif call.name == 'NewRectangleSubset' then
      subsetDefs[call.return_val] = call.args[3]
    elseif call.name == 'NewRelation' then
      rels:insert(call.return_val)
    elseif call.name == 'SetGlobal' then
      -- Do nothing
    else assert(false) end
  end
  -- Emit global declarations
  local globalMap = {} -- map(L.Global, RG.symbol)
  for g,val in pairs(globalInits) do
    local typ = toRType(g:Type())
    local x = RG.newsymbol(typ)
    globalMap[g] = x
    stmts:insert(rquote var [x] = [toRLiteral(typ, val)] end)
  end
  -- Emit region declarations
  local relMap = {} -- map(R.Relation, RG.symbol)
  for _,rel in ipairs(rels) do
    local rg = RG.newsymbol(rel:Name())
    relMap[rel] = rg
    stmts:insert(rquote
      var [rg] = [rel:mkRegionInit()]
    end)
  end
  -- Emit subset declarations
  local subsetMap = {} -- map(R.Subset, RG.symbol)
  for subset,rects in pairs(subsetDefs) do
    local rel = subset:Relation()
    if #rects > 1 then
      print('WARNING: Skipping multi-rect subset '..subset:FullName())
    else
      local rg = relMap[rel]
      local subrg = RG.newsymbol(rel:Name()..'_'..subset:Name())
      subsetMap[subset] = subrg
      local rect = rects[1]
      local rectExpr =
        (#rect == 1) and rexpr
          rect1d{ lo = [ rect[1][1] ],
                  hi = [ rect[1][2] ]}
        end or
        (#rect == 2) and rexpr
          rect2d{ lo = int2d{ x = [ rect[1][1] ],
                              y = [ rect[2][1] ]},
                  hi = int2d{ x = [ rect[1][2] ],
                              y = [ rect[2][2] ]}}
        end or
        (#rect == 3) and rexpr
          rect3d{ lo = int3d{ x = [ rect[1][1] ],
                              y = [ rect[2][1] ],
                              z = [ rect[3][1] ]},
                  hi = int3d{ x = [ rect[1][2] ],
                              y = [ rect[2][2] ],
                              z = [ rect[3][2] ]}}
        end or
        assert(false)
      stmts:insert(rquote
        var colors = ispace(int1d, 1)
        var coloring = RG.c.legion_domain_point_coloring_create()
        var rect = [rectExpr]
        RG.c.legion_domain_point_coloring_color_domain(coloring, int1d(0), rect)
        var [subrg] = partition(disjoint, rg, coloring, colors)
        RG.c.legion_domain_point_coloring_destroy(coloring)
      end)
    end
  end
  -- Emit tasks
  local taskMap = {} -- map(F.Function, RG.task)
  local funInfo = {} -- map(F.Function, Context)
  for _,f in ipairs(funs) do
    taskMap[f], funInfo[f] = f:toTask()
  end
  -- Process commands
  for _,call in ipairs(LOG.log.entries) do
    if call.name == 'ForEachCall' then
      -- call.return_val : {
      --   ...
      --   ufunc    : F.Function
      --   relation : R.Relation
      --   subset   : R.Subset?
      -- }
      local tsk = taskMap[call.return_val.ufunc]
      local info = funInfo[call.return_val.ufunc]
      local univArg = relMap[call.return_val.relation]
      local domArg = call.return_val.subset
        and subsetMap[call.return_val.subset]
        or univArg
      local globalArgs =
        info.readGlobals:map(function(g) return globalMap[g] end)
      -- TODO: Temporary fix until argument splicing is implemented
      -- local callExpr = rexpr [tsk]([domArg], [univArg], [globalArgs]) end
      local callExpr
      if #globalArgs == 0 then
        callExpr = rexpr [tsk]([domArg], [univArg]) end
      elseif #globalArgs == 1 then
        callExpr = rexpr [tsk]([domArg], [univArg],
                               [globalArgs[1]]) end
      elseif #globalArgs == 2 then
        callExpr = rexpr [tsk]([domArg], [univArg],
                               [globalArgs[1]]
                               [globalArgs[2]]) end
      else assert(false) end
      local callQuote = rquote [callExpr] end
      if info.reducedGlobal then
        local retSym = globalMap[info.reducedGlobal]
        local op = info.globalReduceOp
        callQuote =
          (op == '+')   and rquote [retSym] +=   [callExpr] end or
          (op == '-')   and rquote [retSym] -=   [callExpr] end or
          (op == '*')   and rquote [retSym] *=   [callExpr] end or
          (op == '/')   and rquote [retSym] /=   [callExpr] end or
          (op == 'max') and rquote [retSym] max= [callExpr] end or
          (op == 'min') and rquote [retSym] min= [callExpr] end or
          assert(false)
      end
      stmts:insert(callQuote)
    elseif call.name == 'GetGlobal' then
      -- Do nothing
    elseif call.name == 'LoadField' then
      local fld = call.args[1]
      local relSym = relMap[fld:Relation()]
      local typ = toRType(fld:Type())
      local val = call.args[2]
      stmts:insert(rquote
        fill(relSym.[fld:Name()], [toRLiteral(typ, val)])
      end)
    elseif call.name == 'NewField' then
      -- Do nothing
    elseif call.name == 'NewFunction' then
      -- Do nothing
    elseif call.name == 'NewGlobal' then
      -- Do nothing
    elseif call.name == 'NewRectangleSubset' then
      -- Do nothing
    elseif call.name == 'NewRelation' then
      -- Do nothing
    elseif call.name == 'SetGlobal' then
      stmts:insert(rquote
        [globalMap[call.args[1]]] = [call.args[2]]
      end)
    else assert(false) end
  end
  -- Synthesize main task
  local task main()
    [stmts]
  end
  if DEBUG then main:printpretty() end
  RG.start(main)
end
