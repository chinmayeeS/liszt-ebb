Quickstart
==========

* Clone Liszt-Legion (this repo):
  ```
  git clone https://github.com/manopapad/liszt-legion.git <liszt-dir>
  ```

* Clone Legion:
  ```
  git clone -b master https://github.com/StanfordLegion/legion.git <legion-dir>
  ```

* Add to your `~/bashrc`:
  ```
  export LEGION_PATH=<legion-dir>
  ```

* Build Regent (Legion's front-end language):
  ```
  cd <legion-dir>/language
  ./install.py
  ```

* Add at the bottom your Liszt source file:
  ```
  (require 'admiral').translateAndRun()
  ```

* Run your Liszt program as follows:
  ```
  <liszt-dir>/liszt-legion.sh <liszt-source>
  ```
