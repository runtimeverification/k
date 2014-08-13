<!-- Copyright (c) 2010-2014 K Team. All Rights Reserved. -->
This is a readme file for the developers.

# Prerequisites

## Java Development Kit (required JDK7 or higher)
You can follow the instructions here: 
http://docs.oracle.com/javase/7/docs/webnotes/install/index.html depending on 
the type of your machine.

To make sure that everything works you should be able to call `java -version` and
`javac -version` from a Terminal.

## Apache ANT
Linux and Mac:
* Most likely you will already have it.
Windows:
*   Go to http://ant.apache.org/bindownload.cgi and download the zip with the 
    binary distribution. Unzip it in your desired location and follow the 
    installation instructions from the INSTALL file.

Ant usually requires setting an environment variable `JAVA_HOME` pointing
to the installation directory of the JDK (not to be mistaken with JRE).
	
## Git - command line
Having a GUI client is not enough. Most distributions have an installation
option to make git accessible in the command line too.

You can test if it works by calling `ant` in a Terminal.

## (On Windows only) Visual C++ 2012 Redistributable Package
Download here: 
http://www.microsoft.com/en-us/download/details.aspx?id=30679

Make sure to download the 64-bit version if you are using a 64-bit JRE,
and the 32-bit version if you are using a 32-bit JRE.

# Install
Checkout this directory in your desired location and call `ant` from the main
directory to build the .jar binaries. For convenient usage, you can update
your $PATH with <checkout-dir>/bin (strongly recommended, but optional).

# Work on Java code
We here only give instructions for Eclipse, but similar instructions apply
for other IDEs.  Open Eclipse and set your workspace to src/javasources.  Go to
File->Import->General->Existing projects into workspace, and select
the project src/javasources/KTool.  If you need to edit SDF-related code,
you should install the Spoofax plugin and then also import
src/javasources/parsers/Concrete.

# Work on Maude code
Modify the Maude files found in lib/maude/lib. No need for recompilation.

# Build the final release directory/archives
Call `ant release` in the base directory.  This will create a k directory in
trunk containing the release distribution and two archives k-latest.(zip|tgz)

You can use `ant release -Dversion="3.4"` to create a tagged release.

# Compiling definitions and running programs
Assuming k/bin is in your path, you can compile definitions using
the `kompile` command.  To execute a program you can use `krun`.

# Troubleshooting
Common error messages:

- `Unable to find a javac compiler;
  com.sun.tools.javac.Main is not on the classpath.
  Perhaps JAVA_HOME does not point to the JDK.`
  + Make sure `JAVA_HOME` points to the JDK and not the JRE directory.

-  `Execute failed: java.io.IOException: Cannot run program "git":
   CreateProcess error=2, The system cannot find the file specified`
   +  Git is not accessible in the command line. Please reinstall git and make
   make sure to check to option to make it available in the command line.

- Can't find/access AST Node typecom.puppycrawl.tools.checkstyle.api.DetailAST
+ Checkstyle 5.7 is known to be incompatible with version 1.9.2 of the ant antlr
  task. Compatibility with version 1.8.2 is confirmed, and other older versions
  may also be compatible. Checkstyle also works correctly if the antlr ant task
  is not installed.

Sometimes javac dependency resolution fails to recognize changed files and
would fail to build. Try `ant clean` and rebuild the entire project.

If that still doesn't work, please contact a K developer.
