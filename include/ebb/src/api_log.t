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
package.loaded["ebb.src.api_log"] = A

-- API log entry
local APIEntry = {}
APIEntry.__index = APIEntry

local function NewAPIEntry(call_name, args, return_val)
  local entry = setmetatable({}, APIEntry)
  entry.name       = call_name
  entry.args       = args
  entry.return_val = return_val
  return entry
end

-- stringify lua values
local function escape_str(s)
  return string.gsub(s, "\"", "\\\"")
end
local function elem_stringify(k)
  local typ = type(k)
  if      typ == 'number'   then  return tostring(k)
  elseif  typ == 'boolean'  then  return tostring(k)
  elseif  typ == 'string'   then  return string.format('"%s"',escape_str(k))
  else return tostring(k) end
end
function APIEntry:args_stringify()
  local obj = self.args
  local entries = terralib.newlist()
  if terralib.israwlist(obj) then
    for i=1,#obj do entries[i] = elem_stringify(obj[i]) end
  else
    for k,v in pairs(obj) do entries:insert(
      string.format( '[%s]=%s', elem_stringify(k), elem_stringify(v) ))
    end
  end
  return string.format( '{%s}', entries:concat(', ') )
end

function APIEntry:indented_string(indent)
  local str  = indent .. " name : " .. self.name .. "\n"
  str = str .. indent .. " return val : " .. tostring(self.return_val) .. "\n"
  str = str .. indent .. " args : " .. self:args_stringify()
  return str
end


-- Log all Ebb API calls that need to be passed to Legion here

local APILog = { entries = terralib.newlist() }

function APILog:insert(entry)
  self.entries:insert(entry)
end

function APILog:print()
  for k,v in ipairs(self.entries) do
    print("[" .. k .. "]")
    print(v:indented_string("   "))
  end
end

function A.RecordAPICall(call_name, args, return_val)
  assert(type(args) == 'table')
  local entry = NewAPIEntry(call_name, args, return_val)
  APILog:insert(entry)
end

A.log = APILog
