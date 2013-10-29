package org.kframework.utils.errorsystem;

public class KMessages {

	// Errors
	public static final String ERR1001 = "Cannot generate the pdf version of the definition. It seems that `pdflatex` is not installed or is not in your path. To generate the pdf version you can run `pdflatex` having as argument the latex version of the definition.";
	public static final String ERR1003 = "pdflatex returned a non-zero exit code.  The pdf might be generated, but with bugs. please inspect the latex logs in the .k directory.";
	public static final String ERR1004 = "Could not find 'required' file: ";
}
