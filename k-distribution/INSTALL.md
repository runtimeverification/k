---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---
Installing the K Framework
==========================

Fast Installation (preferred)
-----------------------------

The preferred way to install K is the `kup` tool, which is based on [Nix](https://nixos.org/download.html).
No knowledge of Nix is required to use `kup`.

Install `kup` and `K` by running the following:

```shell
bash <(curl https://kframework.org/install)
kup install k
```

List available versions with:

```shell
kup list k
```

If `kup` indicates that there's a newer version, you can update by simply running:

```shell
kup install k
```

To install a specific version, run:

```shell
kup install k --version v6.3.11
```

Note that the versions marked as ✅ are cached in Runtime Verification's Nix binary cache and thus are the fastest to install.

Install through packages
----------------

We currently strive to provide packages for the following platforms:

-   Ubuntu Jammy Jellyfish (22.04)
-   macOS Ventura (13) via Homebrew
-   Docker Images

Pre-installation Notes
----------------------

-   We **do not** currently support running K natively on Windows. To use K on
    Windows 10, you are encouraged to install the
    [Windows Subsystem for Linux (version 2)](https://docs.microsoft.com/en-us/windows/wsl/install-win10)
    and follow the instructions for installing Ubuntu Jammy.

    If you have already installed WSL, before proceeding, you will need to
    enter the WSL environment. You can do this by:

    1.  opening up the command prompt (accessible by searching `cmd` or
        `command prompt` from the start menu);
    2.  using the `wsl.exe` command to access the WSL environment.

-   To use K in other non-linux environments (e.g. Windows 8 or earlier),
    you will need to use a virtual machine (VM) software. We assume you have:

    1.  Created a virtual machine
    2.  Installed a Linux distribution (e.g. Ubuntu Jammy Jellyfish) on your
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

-   K depends on version 4.8.15 of Z3, which may not be supplied by package
    managers. If this is the case, it should be built and installed from source
    following the
    [instructions](https://github.com/Z3Prover/z3#building-z3-using-cmake) in
    the Z3 repository. Other versions (older and newer) are not supported by K,
    and may lead to incorrect behaviour or performance issues.

Downloading Packages
--------------------

Download the appropriate package from the GitHub, via the
[Releases](https://github.com/runtimeverification/k/releases) page.
Releases are generated as often as possible from `master` build.

Installing Packages
-------------------

For version `X.Y.Z`, distribution `DISTRO`, and package ID `ID`, the following
instructions tell you how to install on each system. Note that this typically
requires about ~1.4GB of dependencies and will take some time.

-   On Linux systems, K will typically be installed under `/usr`.
-   On macOS/brew, K will typically be installed under `/usr/local`.

### Ubuntu Jammy (22.04)

```sh
sudo apt install ./kframework_amd64_ubuntu_jammy.deb
```

### macOS (Homebrew)

[Homebrew](https://brew.sh/) (or just brew) is a third-party package manager
for MacOS.
If you have not installed brew, you must do so before installing the K
Framework brew package.

With brew installed, do the following to install the K Framework brew package
(with build number `BN`):

```sh
brew install kframework--X.Y.Z.ID.bottle.BN.tar.gz -v
```

#### Homebrew Alternate Installation

To directly install the latest K Framework brew package without needing to
download it separately, do the following:

```sh
brew install runtimeverification/k/kframework
```

Or, to streamline future K Framework upgrades, you can `tap` the K Framework
package repository. This lets future installations/upgrades/etc... use the
unprefixed package name.

```sh
brew tap runtimeverification/k
brew install kframework
```

### Docker Images

Docker images with K pre-installed are available at the
[runtimeverification/kframework-k Docker Hub repository](https://hub.docker.com/repository/docker/runtimeverificationinc/kframework-k).

Each release at `COMMIT_ID` has an image associated with it at
`runtimeverificationinc/kframework-k:ubuntu-jammy-COMMIT_ID`.

To run the image directly:

```sh
docker run -it runtimeverificationinc/kframework-k:ubuntu-jammy-COMMIT_ID
```

and to make a Docker Image based on it, use the following line in your
`Dockerfile`:

```Dockerfile
FROM runtimeverificationinc/kframework-k:ubuntu-jammy-COMMIT_ID
```

We also create Ubuntu 22.04 images with the `ubuntu-jammy-COMMIT_ID` tags.

Testing Packages
----------------

The easiest way to test the K package is to copy a K tutorial language and
check if you can compile and run an included example.

1.  Start by cloning the K tutorial from the [K PL Tutorial](https://www.github.com/runtimeverification/pl-tutorial). This command typically will be like:

    ```sh
    $ git clone https://www.github.com/runtimeverification/pl-tutorial
    ```

2.  Now you can try to run some programs:

    ```sh
    $ cd pl-tutorial/2_languages/1_simple/1_untyped
    $ make kompile
    $ krun tests/diverse/factorial.simple
    ```
