
This file contains informations for developers who want to
add new examples or issues in the K framework such that they
will be tested by Jenkins: https://fmse.info.uaic.ro/jenkins/



**********************************************
*** Adding new languages to /dist/examples ***
**********************************************

Suppose you want to add an untyped expressions language called "exp-untyped".

General steps:

- The definition:

1) create exp-untyped dir under /dist/examples directory
2) append exp-untyped.k to dir /exp-untyped

- Programs:

3) create directory programs under /exp-untyped directory
4) create program.exp-untyped, an exp program in /programs directory
5) create directory exp-untyped under /tests/examples
6) append program.exp-untyped.in and program.exp-untyped.out in
   /tests/examples/exp-untyped/ dir

For the following special cases:

a) The name of the directory is not similar with the definition name
	e.g: 
		dir: /dist/examples/exp/untyped/exp-untyped.k

b) The name of the main module is not upperCase(exp-untyped)

c) The extension of the programs is not the same as the name of the definition:
	e.g:
		definition: /dist/examples/exp-untyped/exp-untyped.k
		programs: /dist/examples/exp-untyped/programs/program.exp


d) The name of the input and output files for some programs are different:
	e.g:
		program: program.exp
		input file: pgm.in (default should be program.exp.in)
		output file: pgm.out (default should be program.exp.out)

e) Some programs need special options to run


we create in directory /tests/examples/simple-untyped/ a configuration file:
called "config.xml".
For instance, a "config.xml" for simple-unyped may contain:

<config>
	
	<test def="/dist/examples/simple-untyped/simple-untyped.k" 
	      program-extension="simple" 
	      compiled-file-name="simple-untyped-compiled.maude"
	      module-name="SIMPLE-UNTYPED"/>

	<krun-options>
		<program name="collatz.simple" input="collatz.simple.in" 
					       output="collatz.simple.out"/>
			<option name="output-mode" value="none"/>
			<option name="--no-color"/>
		</program>
		<program name="dekker.simple" ignore="yes"/>
		<general>
            <option name="--output-mode" value="pretty"/>
		    <option name="--no-color" value=""/>
		</general>
	</krun-options>
</config>


As you can see in the XML above, some programs (e.g. which 
do not finish) can be ignored by setting ignore attribute to "yes".


*************************
*** Append new issues ***
*************************


An issue is represented by a directory named issue*** where *** is 
the number of the number of the issue on google-code issues page.
This directory contains a file issue***.k and two directories:
- programs: it contains programs of the form: program.issue***
- tests: it contains input and output files: program.issue***.(in/out)

ATENTION: The issue*** directory will be added under /tests/issues directory!

An example can be found in /tests/regression/issue.
