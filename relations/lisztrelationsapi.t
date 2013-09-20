local L = {}
local C = terralib.includecstring [[
    #include <stdlib.h>
    #include <string.h>
]]
local table = {}
table.__index = table
function L.istable(t)
    return getmetatable(t) == table
end

local key = {}

function L.newtable(size, debugname)
    return setmetatable({ _size = size, _fields = terralib.newlist(), _debugname = debugname or "anon" },table)
end

local field = {}

function table:__newindex(fieldname,value)
    local typ = value.type --TODO better error checking
    local f = setmetatable({},field)
    rawset(self,fieldname,f)
    f.name = fieldname
    f.table = self
    f.type = typ
    f.realtype = L.istable(f.type) and uint32 or f.type
    self._fields:insert(f)
end 

field.__index = field
function L.isfield(f)
    return getmetatable(f) == field
end

function L.newfield(t)
    return { type = t } 
end


function field:loadfrommemory(mem)
    assert(self.data == nil)
    local nbytes = self.table._size * terralib.sizeof(self.realtype)
    local bytes = C.malloc(nbytes)
    self.data = terralib.cast(&self.realtype,bytes)
    local memT = terralib.typeof(mem)
    assert(memT == &self.realtype)
    C.memcpy(self.data,mem,nbytes)
end

function table:loadindexfrommemory(fieldname,row_idx)
    assert(self._index == nil)
    local f = self[fieldname]
    assert(f and f.data == nil and L.istable(f.type))
    local realtypesize = terralib.sizeof(f.realtype)
    local nbytes = (f.type._size + 1)*realtypesize
    rawset(self, "_index", terralib.cast(&f.realtype,C.malloc(nbytes)))
    local memT = terralib.typeof(row_idx)
    assert(memT == &f.realtype)
    C.memcpy(self._index,row_idx,nbytes)
    f.data = terralib.cast(&f.realtype,C.malloc(self._size*realtypesize))
    for i = 0, f.type._size - 1 do
        local b = self._index[i]
        local e = self._index[i+1]
        for j = b, e - 1 do
            f.data[j] = i
        end
    end
end


function field:dump()
    print(self.name..":")
    if not self.data then
        print("...not initialized")
        return
    end
    local N = self.table._size
    for i = 0,N - 1 do
        print("",i, self.data[i])
    end
end

function table:dump()
    print(self._debugname, "size: "..self._size)
    for i,f in ipairs(self._fields) do
        f:dump()
    end
end


local cells = L.newtable(4,"cells")
cells.temperature = L.newfield(double)

local data = terralib.cast(&double,terralib.new(double[4],{4,3,2,1}))
cells.temperature:loadfrommemory(data)
cells:dump()


local function newmem(T,data)
    --this is probably not safe... but is just used here for debugging
    return terralib.cast(&T,terralib.new(T[#data],data))
end

local faces = L.newtable(2,"faces")
local edges = L.newtable(9,"edges")

local ftoe = L.newtable(5,"ftoe")
ftoe.face = L.newfield(faces)
ftoe.edge = L.newfield(edges)

ftoe.edge:loadfrommemory(newmem(uint32,{0,1,5,7,8}))
ftoe:loadindexfrommemory("face",newmem(uint32,{0,2,5}))

ftoe:dump()


