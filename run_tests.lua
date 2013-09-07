#!./terra/build/LuaJIT-2.0.1/src/luajit
local ffi = require("ffi")

local lscmd
if ffi.os == "Windows" then
    lscmd = "cmd /c dir /b /s"
else
    lscmd = "find . | cut -c 3-"
end

local passed = {}
local failed = {}

for line in io.popen(lscmd):lines() do
    if ffi.os == "Windows" then
        local cwd = io.popen("cmd /c echo %cd%"):read()
        line = line:sub(cwd:len()+2)
        line = line:gsub("\\","/")
    end
    local file = line:match("^(tests/[^/]*%.t)$") or line:match("^(tests/[^/]*%.lua)$")
    if file and not line:match("tests/test.lua") then
        print(file)
        local execstring = "./liszt " .. file
        --things in the fail directory should cause terra compiler errors
        --we dont check for the particular error
        --but we do check to see that the "Errors reported.." message prints
        --which suggests that the error was reported gracefully
        --(if the compiler bites it before it finishes typechecking then it will not print this)
        local success = os.execute(execstring)
        if success ~= 0 then
            table.insert(failed,file)
        else
            table.insert(passed,file)
        end
    end
end

local function printtests(nm,lst)
    if #lst > 0 then
        print("=================")
        print("= "..nm)
        print("=================")
        for i,e in ipairs(lst) do
            print(e)
        end
        print("=================")
        print()
    end
end
printtests("passing tests",passed)
printtests("FAILING tests",failed)
print(tostring(#passed).." tests passed. "..tostring(#failed).." tests failed.")
