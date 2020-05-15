Installing K Framework Package
==============================

We currently strive to provide packages for the following platforms:

-   Ubuntu Bionic (18.04)
-   Debian Buster
-   Arch Linux
-   MacOS X Mojave
-   Docker Images
-   Platform Independent K Binary

**NOTE**: We do not currently support running K on native Windows. To use K on
Windows, you are encouraged to install
[Windows Subsystem for Linux](https://docs.microsoft.com/en-us/windows/wsl/install-win10)
and follow the instructions for Ubuntu Bionic.

Download Packages
-----------------

Download the appropriate package from the GitHub, via the
[Releases](https://github.com/kframework/k/releases) page.
Releases are generated as often as possible from `master` build.

Install Packages
----------------

For version `X.Y.Z`, disto `DISTRO`, and package ID `ID`, the following
instructions tell you how to install on each system.

### Ubuntu Bionic (18.04)/Debian Buster

```sh
sudo apt install ./kframework_X.Y.Z_amd64_DISTRO.deb
```

### Arch Linux

```sh
pacman -U ./kframework-git-X.Y.Z-1-x86_64.pkg.tar.xz
```

### MacOS X Mojave

Tap the `kframework/k` bottle then install (with build number `BN`):

```sh
brew tap kframework/k "file:///$(pwd)"
brew install kframework--X.Y.Z.ID.bottle.BN.tar.gz -v
```

### Docker Images

Docker images with K pre-installed are available at the
[runtimeverification/kframework-k Docker Hub repository](https://hub.docker.com/repository/docker/runtimeverificationinc/kframework-k).

Each release at `COMMIT_ID` has an image associated with it at
`runtimeverificationinc/kframework-k:ubuntu-bionic-COMMIT_ID`.
The latest `master` build Docker image can be accessed with `COMMIT_ID` set to
`master`.

To run the image directly:

```sh
docker run -it runtimeverificationinc/kframework-k:ubuntu-bionic-COMMIT_ID
```

and to make a Docker Image based on it, use the following line in your
`Dockerfile`:

```Dockerfile
FROM runtimeverificationinc/kframework-k:ubuntu-bionic-COMMIT_ID
```

### Platform Independent K Binary

The platform independent K binary is a best-attempt at making a portable
distribution of K. When possible, prefer the platform specific packages.
We have only tested this on Ubuntu, although it may work on other distributions.
Appropriate installation instructions and bug reports are welcome from
contributors.

1.  Install Prerequisites:

    ```sh
    sudo apt-get update
    sudo apt-get install build-essential m4 openjdk-8-jre libgmp-dev libmpfr-dev pkg-config flex bison z3 libz3-dev unzip python3
    ```

2.  Unpack the binary (will place in subdirectory `k`), move to preferred install location:

    ```sh
    tar -xvf kframework-X.Y.Z-ID-x86_64.pkg.tar.gz
    mv k /PATH/TO/INSTALL/k
    ```

3.  Update your `PATH` (using the `k` directory extracted to above):

    ```sh
    export PATH=$PATH:/PATH/TO/INSTALL/k/bin
    ```

4.  Install OCaml (Optional):

    **NOTE**: It is *strongly* recommended that you use the LLVM backend
    instead of the OCaml backend. The OCaml backend is being sunsetted.

    To use the OCAML backend requires an installation of the OCAML package
    manager OPAM. Instructions on installing OPAM are available here:
    <https://opam.ocaml.org/doc/Install.html>.
    You should install on Windows by following the instructions for the Linux
    distribution you installed for Windows Subsystem for Linux.

    Once opam is installed, you can prepare the installation to run the OCAML
    backend by running:

    ```
    k-configure-opam
    eval $(opam config env)
    ```

    `k-configure-opam` is in the `k/bin` directory, and the `eval` command sets
    up your OCaml environment.

4. Test:

   Go to one of the examples (say `k/tutorial/2_languages/1_simple/1_untyped/`).
   Assuming `k/bin` is in your `$PATH`, you can compile and test a definition by
   running the `make` command. To execute a program you can use e.g.
   `krun tests/diverse/factorial.simple`. K supports both the LLVM/OCaml
   backends for concrete execution and the Haskell/Java backend for symbolic
   execution and program verification (with `kompile --backend [haskell|java]`).
