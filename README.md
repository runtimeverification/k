---
permalink: README.html
copyright: Copyright (c) 2010-2020 K Team. All Rights Reserved.
---

[Join the chat at Riot](https://riot.im/app/#/room/#k:matrix.org)

# Introduction

This is a readme file for _K developers_.

_K-based tool users_ should:

1.  Consult their tool documentation for build/installation instructions.
2.  If needed, download a [packaged release](https://github.com/kframework/k/releases/)
    of the K Framework as part of their tool setup process.

The rest of this file assumes you intend to build and install the K Framework
from source.

# Prerequisite Install Guide

Before building and installing the K Framework, the following prerequisites
must first be installed.

## The Short Version

On Ubuntu Linux:

```
git submodule update --init --recursive
sudo apt-get install build-essential m4 openjdk-8-jdk libgmp-dev libmpfr-dev pkg-config flex bison z3 libz3-dev maven python3 cmake gcc clang-8 lld-8 llvm-8-tools zlib1g-dev libboost-test-dev libyaml-dev libjemalloc-dev
curl -sSL https://get.haskellstack.org/ | sh
```

On Arch Linux:

```
git submodule update --init --recursive
sudo pacman -S git maven jdk-openjdk cmake boost libyaml jemalloc clang llvm lld zlib gmp mpfr z3 curl stack base-devel base python
```

If you install this list of dependencies, continue directly to the [Build and Install Guide](#build-and-install-guide).

## The Long Version

### Java Development Kit (required JDK8 version 8u45 or higher)

Linux:
*   Download from package manager (e.g. `sudo apt-get install openjdk-8-jdk`)

To make sure that everything works you should be able to call `java -version` and
`javac -version` from a Terminal.

### Apache Maven

Linux:
*   Download from package manager (e.g. `sudo apt-get install maven`)

Mac:
*   Download it from a package manager or from
    http://maven.apache.org/download.cgi and follow the instructions on the webpage.

Maven usually requires setting an environment variable `JAVA_HOME` pointing
to the installation directory of the JDK (not to be mistaken with JRE).

You can test if it works by calling `mvn -version` in a Terminal.
This will provide the information about the JDK Maven is using, in case
it is the wrong one.

### Haskell Stack

To install, go to <https://docs.haskellstack.org/en/stable/README/> and follow the instructions.
You may need to do `stack upgrade` to ensure the latest version of Haskell Stack.

### Miscellaneous

Also required:

*   [gcc](https://gcc.gnu.org/)
*   [flex](https://github.com/westes/flex)
*   [make](https://www.gnu.org/software/make/)
*   [gmp](https://gmplib.org/)
*   [mpfr](http://www.mpfr.org/)
*   [pkg-config](https://www.freedesktop.org/wiki/Software/pkg-config/)
*   [z3](https://github.com/Z3Prover/z3)
*   [python](https://www.python.org)
*   [opam](https://opam.ocaml.org/doc/Install.html) **OPTIONAL**

These can all be installed from your package manager.

# Build and Install Guide

Checkout the project source at your desired location and call `mvn package` from the main
directory to build the distribution. For convenient usage, you can update
your $PATH with <checkout-dir>k-distribution/target/release/k/bin (strongly recommended, but optional).

You are also encouraged to set the environment variable `MAVEN_OPTS` to `-XX:+TieredCompilation`,
which will significantly speed up the incremental build process.

**IF** you want to use the OCAML backend (not recommended), you need to install
the following dependencies:

-   [pkg-config](https://www.freedesktop.org/wiki/Software/pkg-config/)
-   [opam](https://opam.ocaml.org/)

and then after running `mvn package` for the first time, setup OCAML dependencies:

```sh
k-distribution/target/release/k/bin/k-configure-opam
eval $(opam config env)
```

This performs first-time setup of the OCAML backend. You may optionally set
`OPAMROOT` before running this command to specify where the OCAML dependencies
should be installed to.

## Installing on fresh Windows Subsystem for Linux

1. Install the Ubuntu package from the Windows Store, which as of now is an alias for the Ubuntu LTS 18.04 package. During installation you will be asked to create a new user.
2. Download the latest K distribution for Ubuntu Bionic from https://github.com/kframework/k/releases
    to a temporary directory, for example `d:\temp`

3. Open linux bash. For example by running:
```
ubuntu1804
```

4. Run the following commands:

    `$ sudo apt-get update`

    `$ cd <download dir>`. In our example download dir is `/mnt/d/temp`

    `$ sudo apt-get install ./kframework_5.0.0_amd64_bionic.deb`
        This will install ~1.4GB of dependencies and will take some time.
        K will be installed to `/usr`

5. Copy the tutorial to some work directory, for example `/mnt/d/k-tutorial`. Otherwise, you won't be able to run the
examples from default installation dir if you are not `root`:

```
$ cp -R /usr/share/kframework/tutorial /mnt/d/k-tutorial
```

6. Now you can try to run some programs:

```bash
$ cd /mnt/d/k-tutorial/2_languages/1_simple/1_untyped
$ make kompile
$ krun tests/diverse/factorial.simple
```

# Building with Nix

To build the K Framework itself, run:

```bash
nix-build -A k
```

The various backends are provided as separate packages:

```bash
nix-build -A llvm-backend
nix-build -A haskell-backend
```

To run the integration tests:

```bash
nix-build test.nix
```

You can enter a development environment for working on the K Framework frontend
by running:

```bash
nix-shell
```

To create a development environment for a project that depends on the K
Framework, you can add a `shell.nix` based on this template:

```.nix
# shell.nix
let
  kframework = import ./path/to/k {};
  inherit (kframework) mkShell;
in
mkShell {
  buildInputs = [
    kframework.k
    clang kframework.llvm-backend
    kframework.haskell-backend
  ];
}
```

If you change any `pom.xml`, you must run `./nix/update-maven.sh`.

# IDE Setup

## General

You should run K from the k-distribution project, because it is the only project to have the complete
classpath and therefore all backends.

## Eclipse
_N.B. the Eclipse internal compiler may generate false compilation errors (there are bugs in its support of Scala mixed compilation). We recommend using IntelliJ IDEA if at all possible._

To autogenerate an Eclipse project for K, run `mvn install -DskipKTest; mvn eclipse:eclipse` on the
command line, and then go into each of the `kore` and `tiny` directories and run `sbt eclipse`.
Then start eclipse and go to File->Import->General->Existing projects into workspace, and select
the directory of the installation. You should only add the leaves to the workspace, because
eclipse does not support hierarchical projects.

## IntelliJ IDEA

IntelliJ IDEA comes with built-in maven integration. For more information, refer to
the [IntelliJ IDEA wiki](http://wiki.jetbrains.net/intellij/Creating_and_importing_Maven_projects)

# Running the Test Suite

To completely test the current version of the K framework, run `mvn verify`.
This normally takes roughly 30 minutes on a fast machine. If you are interested only
in running the unit tests and checkstyle goals, run `mvn verify -DskipKTest` to
skip the lengthy `ktest` execution.

# Changing the KORE Data Structures
If you need to change the KORE data structures (unless you are a K core developer, you probably do not), see [Guide-for-changing-the-KORE-data-structures](https://github.com/kframework/k/wiki/Guide-for-changing-the-KORE-data-structures).

# Building the Final Release Directory/Archives
Call `mvn install` in the base directory. This will attach an artifact to the local
maven repository containing a zip and tar.gz of the distribution.

The functionality to create a tagged release is currently incomplete.

# Compiling Definitions and Running Programs
Assuming k-distribution/target/release/k/bin is in your path, you can compile definitions using
the `kompile` command.  To execute a program you can use `krun`.

For running either program in the debugger, use the main class `org.kframework.main.Main` with an additional argument `-kompile` or `-krun` added before other command line arguments, and use the classpath from the `k-distribution` module.

# Troubleshooting
Common build-time error messages:

-   `Error: JAVA_HOME not found in your environment.
     Please set the JAVA_HOME variable in your environment to match the
     location of your Java installation.`
    + Make sure `JAVA_HOME` points to the JDK and not the JRE directory.

-   `[WARNING] Cannot get the branch information from the git repository:
     Detecting the current branch failed: 'git' is not recognized as an internal or external command,
     operable program or batch file.`
    + `git` might not be installed on your system. Make sure that you can execute
      `git` from the command line.

-   `1) Error injecting constructor, java.lang.Error: Unresolved compilation problems:
          The import org.kframework.parser.outer.Outer cannot be resolved
          Outer cannot be resolved`
    + You may run into this issue if target/generated-sources/javacc is not added to the
      build path of your IDE. Generally this is solved by regenerating your project /
      re-syncing it with the pom.xml.

-   `[ERROR] Failed to execute goal org.apache.maven.plugins:maven-compiler-plugin:3.1:compile
     (default-compile) on project k-core: Fatal error compiling: invalid target release: 1.8 -> [Help 1]`
    + You either do not have Java 8 installed, or `$JAVA_HOME` does not point to a Java 8 JDK.

-   `[ERROR] Failed to execute goal org.apache.maven.plugins:maven-antrun-plugin:1.7:run
     (build-haskell) on project haskell-backend: An Ant BuildException has occured: exec returned: 1`

    and scrolling up, you see an error message similar to:

    `[exec] Installing GHC ...
     [exec] ghc-pkg: Couldn't open database $HOME/.stack/programs/x86_64-linux/ghc-tinfo6-8.10.1/lib/ghc-8.10.1/package.conf.d for modification:
     {handle: $HOME/.stack/programs/x86_64-linux/ghc-tinfo6-8.10.1/lib/ghc-8.10.1/package.conf.d/package.cache.lock}:
     hLock: invalid argument (Invalid argument)`
    + If you are using a [WSL version 1 environment](https://docs.microsoft.com/en-us/windows/wsl/compare-versions),
      then you have encountered a known issue with the latest versions of GHC. In this
      case, please either:
      -   upgrade to [WSL version 2](https://docs.microsoft.com/en-us/windows/wsl/install-win10),
      -   install a [packaged release for your WSL version 1 distribution](https://github.com/kframework/k/releases/),
      -   switch to a supported system configuration (e.g. Linux on a virtual machine), or
      -   if you do not need the symbolic execution capabilities of the K Framework, disable them
          at build time (and remove the GHC dependency) by doing: `mvn package -Dhaskell.backend.skip`.

If something unexpected happens and the project fails to build, try `mvn clean` and
rebuild the entire project. Generally speaking, however, the project should build incrementally
without needing to be cleaned first.

If you are doing work with snapshot dependencies, you can update them to the latest version by
running maven with the `-U` flag.

If you are configuring artifacts in a repository and need to purge the local repository's cache
of artifacts, you can run `mvn dependency:purge-local-repository`.

If tests fail but you want to run the build anyway to see what happens, you can use `mvn package -DskipTests`.

If you still cannot build, please contact a K developer.
