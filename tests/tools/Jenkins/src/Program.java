

public class Program extends Thread{
	public String filename, inputFile, outputFile, krun, kdefinition;

	public Program(String filename, String inputFile, String outputFile,
			String krun, String kdefinition) {
		super();
		this.filename = filename;
		this.inputFile = inputFile;
		this.outputFile = outputFile;
		this.krun = krun;
		this.kdefinition = kdefinition;
	}
	
	@Override
	public void run() {
		super.run();
	}
	
	
	@Override
	public String toString() {
		return "Testing " + filename + " ... ";
	}
}
