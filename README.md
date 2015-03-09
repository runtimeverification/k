<!-- Copyright (c) 2010-2015 K Team. All Rights Reserved. -->
This is a readme file for the developers.

# Prerequisites

## Java Development Kit (required JDK8 or higher)
You can follow the instructions http://docs.oracle.com/javase/8/docs/technotes/guides/install/install_overview.html depending on
the type of your machine.

To make sure that everything works you should be able to call `java -version` and
`javac -version` from a Terminal.

## Apache Maven

Linux:
*   Download from package manager (e.g. `sudo apt-get install maven`)

Mac:
*   If your version is prior to Mavericks, Maven comes pre-installed with XCode.
    Otherwise, download it from a package manager or from
    http://maven.apache.org/download.cgi and follow the instructions on the webpage.

Windows:
*   Go to http://maven.apache.org/download.cgi and download the zip with the 
    binary distribution. Unzip it in your desired location and follow the 
    installation instructions on the webpage.

Maven usually requires setting an environment variable `JAVA_HOME` pointing
to the installation directory of the JDK (not to be mistaken with JRE).

You can test if it works by calling `mvn -version` in a Terminal.
This will provide the information about the JDK Maven is using, in case
it is the wrong one.
	
## Git - command line
Having a GUI client is not enough. Most distributions have an installation
option to make git accessible in the command line too.

# Install
Checkout this directory in your desired location and call `mvn package` from the main
directory to build the distribution. For convenient usage, you can update
your $PATH with <checkout-dir>k-distribution/target/release/k/bin (strongly recommended, but optional).

You are also encouraged to set the environment variable `MAVEN_OPTS` to `-XX:+TieredCompilation`,
which will significantly speed up the incremental build process.

# IDE Setup

## General

You should run K from the k-distribution project, because it is the only project to have the complete
classpath and therefore all backends.

## Environment

In order for K to run correctly in an IDE, it is necessary that the correct environment variables be set.

### Mac OS X

`PATH=$PATH:<release>/lib/native/osx
DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:<release>/lib/native/osx`

### Windows x86

`PATH=$PATH;<release>\lib\native\windows;<release>\lib\native\windows32;<release>\lib\native\32`

### Windows x64

`PATH=$PATH;<release>\lib\native\windows;<release>\lib\native\windows64;<release>\lib\native\64`

### Linux i386

`PATH=$PATH:<release>/lib/native/linux:<release>/lib/native/linux32
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:<release>/lib/native/linux32`

### Linux amd64

`PATH=$PATH:<release>/lib/native/linux:<release>/lib/native/linux64
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:<release>/lib/native/linux64`

## Eclipse
To autogenerate an Eclipse project for K, run `mvn install -DskipKTest; mvn eclipse:eclipse` on the
command line. Then go to
File->Import->General->Existing projects into workspace, and select
the directory of the installation. You should only add the leaves to the workspace, because
eclipse does not support hierarchical projects.

## IntelliJ IDEA

IntelliJ IDEA comes with built-in maven integration. For more information, refer to
the [IntelliJ IDEA wiki](http://wiki.jetbrains.net/intellij/Creating_and_importing_Maven_projects)

# Run test suite
To completely test the current version of the K framework, run `mvn verify`.
This normally takes roughly 30 minutes on a fast machine. If you are interested only
in running the unit tests and checkstyle goals, run `mvn verify -DskipKTest` to
skip the lengthy `ktest` execution.

# Changing the KORE data structures
If you need to change the KORE data structures (unless you are a K core developer, you probabably do not), see [Guide-for-changing-the-KORE-data-structures](https://github.com/kframework/k/wiki/Guide-for-changing-the-KORE-data-structures).

# Build the final release directory/archives
Call `mvn install` in the base directory. This will attach an artifact to the local
maven repository containing a zip and tar.gz of the distribution.

The functionality to create a tagged release is currently incomplete.

# Compiling definitions and running programs
Assuming k-distribution/target/release/k/bin is in your path, you can compile definitions using
the `kompile` command.  To execute a program you can use `krun`.

For running either program in the debugger, use the main class `org.kframework.main.Main` with an additional argument `-kompile` or `-krun` added before other command line arguments, and use the classpath from the `k-distribution` module.

# Cross platform compilation
To build a version of the K framework for a platform other than the current version,
you can specify the OS and architecture using profiles. For example, to build a 32-bit
windows release of the K framework, run `mvn install -P windows -P x86 -DskipTests -DskipKTest`.

To view the platform being used by a particular build, run the `mvn help:active-profiles` target.

# Troubleshooting
Common error messages:

-  `Error: JAVA_HOME not found in your environment.
    Please set the JAVA_HOME variable in your environment to match the
    location of your Java installation.`
    + Make sure `JAVA_HOME` points to the JDK and not the JRE directory.

- `[WARNING] Cannot get the branch information from the git repository:
   Detecting the current branch failed: 'git' is not recognized as an internal or external command,
   operable program or batch file.`
   + ``git` might not be installed on your system. Make sure that you can execute
      `git` from the command line.

- `1) Error injecting constructor, java.lang.Error: Unresolved compilation problems:
        The import org.kframework.parser.outer.Outer cannot be resolved
        Outer cannot be resolved`
   + You may run into this issue if target/generated-sources/javacc is not added to the
     build path of your IDE. Generally this is solved by regenerating your project /
     re-syncing it with the pom.xml.

- `[ERROR] Failed to execute goal org.apache.maven.plugins:maven-compiler-plugin:3.1:compile
   (default-compile) on project k-core: Fatal error compiling: invalid target release: 1.8 -> [Help 1]`
   + You either do not have Java 8 installed, or `$JAVA_HOME` does not point to a Java 8 JDK.

If something unexpected happens and the project fails to build, try `mvn clean` and
rebuild the entire project. Generally speaking, however, the project should build incrementally
without needing to be cleaned first.

If you are doing work with snapshot dependencies, you can update them to the latest version by
running maven with the -U flag.

If you are configuring artifacts in a repository and need to purge the local repository's cache
of artifacts, you can run `mvn dependency:purge-local-repository`.

If tests fail but you want to run the build anyway to see what happens, you can use `mvn package -DskipTests`.

If you still cannot build, please contact a K developer.
