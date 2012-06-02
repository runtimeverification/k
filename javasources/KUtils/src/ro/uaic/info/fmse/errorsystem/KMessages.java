package ro.uaic.info.fmse.errorsystem;

public class KMessages {

	// Errors 
	public static final String ERR1000 = "";
	public static final String ERR1001 = "Cannot generate the pdf version of the definition. It seems that `pdflatex` is not installed or is not in your path. To generate the pdf version you can run `pdflatex` having as argument the latex version of the definition.";
	public static final String ERR1002 = "Could not find main module: ";
	public static final String ERR1003 = "pdflatex returned a non-zero exit code.  The pdf might be generated, but with bugs. please inspect the latex logs in the .k directory.";
	
	// Warnings
	public static final String WARNING1000 = "Cannot infer list terminator. This occurs when the compiler appends automatically the list terminator.";

	// Status
	public static final String STATUS1000 = "";

}
