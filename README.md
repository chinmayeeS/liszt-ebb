Quickstart
==========

* Install required packages:
  ```
  sudo apt-get install libhdf5-dev
  ```

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

  - If you're running Debian 8 / Ubuntu 14.04 or older:
    ```
    cd <legion-dir>/language
    ./install.py --hdf
    ```

  - Otherwise:
    ```
    cd <legion-dir>/language
    HDF_LIBNAME=hdf5_serial ./install.py --hdf
    ```

* Add to the bottom your Liszt source file:
  ```
  (require 'admiral').translateAndRun()
  ```

* Run your Liszt program as follows:
  ```
  <liszt-dir>/liszt-legion.sh <liszt-source>
  ```

* Alternatively, you can compile your Liszt program into a binary:
  ```
  SAVEOBJ=1 OBJNAME=<executable> <liszt-dir>/liszt-legion.sh <liszt-source>
  ```
  You can run the output binary as follows:
  ```
  LD_LIBRARY_PATH=<legion-dir>/bindings/terra/ <executable>
  ```
