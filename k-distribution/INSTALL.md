Installing the K Framework Package
==================================

We currently strive to provide packages for the following platforms:

-   Ubuntu Bionic Beaver (18.04) and Focal Fossa (20.04)
-   Debian Bullseye
-   Arch Linux
-   MacOS X Mojave/Homewbrew
-   Docker Images

Pre-installation Notes
----------------------

-   We **do not** currently support running K natively on Windows. To use K on
    Windows 10, you are encouraged to install the
    [Windows Subsystem for Linux (version 2)](https://docs.microsoft.com/en-us/windows/wsl/install-win10)
    and follow the instructions for installing Ubuntu Bionic.

    If you have already installed WSL, before proceeding, you will need to
    enter the WSL environment. You can do this by:

    1.  opening up the command prompt (accessible by searching `cmd` or
        `command prompt` from the start menu);
    2.  using the `wsl.exe` command to access the WSL environment.

-   To use K in other non-linux environments (e.g. Windows 8 or earlier),
    you will need to use a virtual machine (VM) software. We assume you have:

    1.  Created a virtual machine
    2.  Installed a Linux distribution (e.g. Ubuntu Bionic Beaver) on your
        virtual machine

    Consult your virtual machine software if you need help with the above
    steps. We recommend the free VirtualBox virtual machine software.

    Before proceeding, follow the virtual machine softare UI to start your
    Linux virtual machine and enter the command line environment.

-   WSL and virtual machine users should be aware that, if you use your web
    browser to download the package, you will need to make it accessible to
    the command line environment. For this reason, we recommend downloading the
    package from the command line directly using a tool like `wget`. For
    example, you could copy the package download URL and then type:

    ```
    wget <package-download-url>
    ```

    where `<package-download-url>` is replaced by the URL you just copied.

-   The packages we distribute do **not** include the OCaml backend dependency
    setup. However, we include
    [instructions below](#installing-the-ocaml-backend-optional) on using the
    OCaml backend with the package-installed K.

-   K depends on version 4.8.11 of Z3, which may not be supplied by package
    managers. If this is the case, it should be built and installed from source
    following the
    [instructions](https://github.com/Z3Prover/z3#building-z3-using-cmake) in
    the Z3 repository. Other versions (older and newer) are not supported by K,
    and may lead to incorrect behaviour or performance issues.

Downloading Packages
--------------------

Download the appropriate package from the GitHub, via the
[Releases](https://github.com/kframework/k/releases) page.
Releases are generated as often as possible from `master` build.

Installing Packages
-------------------

For version `X.Y.Z`, disto `DISTRO`, and package ID `ID`, the following
instructions tell you how to install on each system. Note that this typically
requires about ~1.4GB of dependencies and will take some time.

-   On Linux systems, K will typically be installed under `/usr`.
-   On macOS/brew, K will typically be installed under `/usr/local`.

### Ubuntu Bionic (18.04)

```sh
sudo apt install ./kframework_X.Y.Z_amd64_bionic.deb
```

### Ubuntu Focal (20.04)

```sh
sudo apt install ./kframework_X.Y.Z_amd64_focal.deb
```

### Debian Bullseye

```sh
sudo apt install ./kframework_X.Y.Z_amd64_bullseye.deb
```

### Arch Linux

```sh
pacman -U ./kframework-git-X.Y.Z-1-x86_64.pkg.tar.zst
```

### MacOS X Mojave/Homebrew

[Homebrew](https://brew.sh/) (or just brew) is a third-party package manager
for MacOS.
If you have not installed brew, you must do so before installing the K
Framework brew package.

With brew installed, do the following to install the K Framework brew package
(with build number `BN`):

```sh
brew install kframework--X.Y.Z.ID.bottle.BN.tar.gz -v
```

Note: the brew package should install on MacOS X Catalina systems even though
the package was built for Mojave.

#### Homebrew Alternate Installation

To directly install the latest K Framework brew package without needing to
download it separately, do the following:

```sh
brew install kframework/k/kframework
```

Or, to streamline future K Framework upgrades, you can `tap` the K Framework
package repository. This lets future installations/upgrades/etc... use the
unprefixed package name.

```sh
brew tap kframework/k
brew install kframework
```

### Docker Images

Docker images with K pre-installed are available at the
[runtimeverification/kframework-k Docker Hub repository](https://hub.docker.com/repository/docker/runtimeverificationinc/kframework-k).

Each release at `COMMIT_ID` has an image associated with it at
`runtimeverificationinc/kframework-k:ubuntu-focal-COMMIT_ID`.
The latest `master` build Docker image can be accessed with `COMMIT_ID` set to
`master`.

To run the image directly:

```sh
docker run -it runtimeverificationinc/kframework-k:ubuntu-focal-COMMIT_ID
```

and to make a Docker Image based on it, use the following line in your
`Dockerfile`:

```Dockerfile
FROM runtimeverificationinc/kframework-k:ubuntu-focal-COMMIT_ID
```

We also create Ubuntu 18.04 images with the `ubuntu-bionic-COMMIT_ID` tags.

Installing the OCaml Backend (Optional)
---------------------------------------

**NOTE**: It is *strongly* recommended that you use the LLVM backend instead of
the OCaml backend. The OCaml backend is being sunsetted.

To use the OCaml backend requires an installation of the OCaml package manager
`opam`. Instructions on installing `opam` are available here:
<https://opam.ocaml.org/doc/Install.html>.
You should install on Windows by following the instructions for the Linux
distribution you installed for Windows Subsystem for Linux.

Once `opam` is installed, you can prepare the installation to run the OCaml
backend by running (for a user-local install):

```sh
k-configure-opam
eval $(opam config env)
```

`k-configure-opam` is in the `k/bin` directory, and the `eval` command sets up
your OCaml environment. You can optionally control where the OCaml dependencies
are installed by setting the `OPAMROOT` environment variable before running the
above commands with `export OPAMROOT=/path/to/opam/root`.

Testing Packages
----------------

The easiest way to test the K package is to copy a K tutorial language and
check if you can compile and run an included example.

1.  Start by copying the K tutorial to some work directory
    (e.g. `$HOME/pl-tutorial`) from the K distribution root. Using a Linux
    package, this command typically will be like:

    ```sh
    $ cp -R /usr/share/kframework/pl-tutorial $HOME/pl-tutorial
    ```

    On macOS/brew, this command typically will be like:

    ```sh
    $ cp -R /usr/local/share/kframework/pl-tutorial $HOME/pl-tutorial
    ```

    This step is needed because sometimes only the `root` user can run the
    examples in the default installation directory.

2.  Now you can try to run some programs:

    ```sh
    $ cd $HOME/pl-tutorial/2_languages/1_simple/1_untyped
    $ make kompile
    $ krun tests/diverse/factorial.simple
    ```
