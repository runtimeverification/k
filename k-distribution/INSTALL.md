<!-- Copyright (c) 2012-2015 K Team. All Rights Reserved. -->
Here are instructions for installing K from the release zip/tgz archive.

1. Prerequisites:
  * Package dependencies:
    `sudo apt-get install build-essential m4 openjdk-8-jre libgmp-dev libmpfr-dev pkg-config flex z3`

2. Install:
  * Unzip this directory in your preferred location.  For convenient usage,
    update your $PATH with <preferred-location>/k/bin.

3. Test:
  * Go to one of the examples (say k/tutorial/2_languages/1_simple/1_untyped/).
    Assuming k/bin is in your $PATH, you can compile definitions using 
    the `kompile simple-untyped.k` command.
    To execute a program you can use `krun tests/diverse/factorial.simple`.

4. (Optional) OCAML:
  * To use the OCAML backend requires an installation of the OCAML package
    manager OPAM. Instructions on installing OPAM are available here:
    https://opam.ocaml.org/doc/Install.html
  * Once opam is installed, you can prepare the installation to run
    the OCAML backend by running the "k-configure-opam" script found
    in the bin directory. You will also need to run ``eval `opam config env` ``
    afterwards to update your environment.

--------------------------------------------------------------------------

Note: We do not currently support running K on native Windows. To use K on
Windows, you are encouraged to install
[Windows Subsystem for Linux](https://docs.microsoft.com/en-us/windows/wsl/install-win10).

--------------------------------------------------------------------------
