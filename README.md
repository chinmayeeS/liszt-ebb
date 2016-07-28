Quickstart
==========

* Clone Liszt-Legion (this repo)
* Install Legion
* Add to your Liszt source file:
  - at the top:
    ```
    local A = require 'admiral'
    ```
  - at the bottom:
    ```
    A.translateAndRun()
    ```
* Run your Liszt program as follows:
  ```
  TERRA_PATH=<liszt-legion-dir>/include/?.t <legion-dir>/language/regent.py <liszt-source>
  ```
