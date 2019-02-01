<!-- Copyright (c) 2012-2019 K Team. All Rights Reserved. -->
Here are instructions for installing K from the release tar.gz archive. If you have installed via the distro package, you do not need to follow these instructinos

We have only tested this on Ubuntu, although it may work on other distributions.
Appropriate installation instructions and bug reports are welcome from contributors.

1. Prerequisites:
  * Package dependencies:
    `sudo apt-get update; sudo apt-get install build-essential m4 openjdk-8-jre libgmp-dev libmpfr-dev pkg-config flex z3 libz3-dev unzip python3`

2. Install:
  * Move this directory, once extracted, to your preferred location.  For convenient usage,
    update your $PATH with <preferred-location>/k/bin.

3. OCAML (not required by K tutorial):
  * To use the OCAML backend requires an installation of the OCAML package
    manager OPAM. Instructions on installing OPAM are available here:
    https://opam.ocaml.org/doc/Install.html
    You should install on Windows by following the instructions for the
    Linux distribution you installed for Windows Subsystem for Linux.
    
  * Once opam is installed, you can prepare the installation to run
    the OCAML backend by running the "k-configure-opam" script found
    in the bin directory. You will also need to run ``eval `opam config env` ``
    afterwards to update your environment.

4. Test:
  * Go to one of the examples (say k/tutorial/2_languages/1_simple/1_untyped/).
    Assuming k/bin is in your $PATH, you can compile and test a definition by running
    the `make` command.
    To execute a program you can use e.g. `krun tests/diverse/factorial.simple`.
    K supports both the OCAML backend for concrete execution (by default) and
    also the Java backend for symbolic execution and program verification (with
    `kompile --backend java`.

--------------------------------------------------------------------------

Note: We do not currently support running K on native Windows. To use K on
Windows, you are encouraged to install
[Windows Subsystem for Linux](https://docs.microsoft.com/en-us/windows/wsl/install-win10).

--------------------------------------------------------------------------
