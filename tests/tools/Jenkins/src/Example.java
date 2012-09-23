import java.io.File;
import java.util.List;
import java.util.concurrent.Executors;
import java.util.concurrent.ThreadPoolExecutor;

public class Example extends Thread {
	String dir;
	String mainFile;
	String compiledFile;
	String mainModule;
	private boolean timedout = false;

	String[] krunOptions;
	String k3jar;
	public List<Program> programs;
	String output = "", error = "";
	int exitCode;
	public boolean runPrograms;
	private long time = 0;
	public String tagName;
	
	public Example(String dir, String mainFile, String mainModule,
			String[] krunOptions, String k3jar, String compiledFile,
			List<Program> programs, String tagName) {
		super();
		this.dir = dir;
		this.mainFile = mainFile;
		this.mainModule = mainModule;
		this.krunOptions = krunOptions;
		this.k3jar = k3jar;
		this.programs = programs;
		this.compiledFile = compiledFile;
		this.tagName = tagName;
	}

	@Override
	public void run() {
		if (!runPrograms) {
			new File(dir + System.getProperty("file.separator")
					+ compiledFile).delete();
			
			// compile the definition: java -ss8m -Xms64m -Xmx1G -jar
			long millis = System.currentTimeMillis();
			Executor compile = new Executor(new String[] { "java", "-ss8m",
					"-Xms64m", "-Xmx1G", "-jar", k3jar, "-kompile", mainFile,
					"-l", mainModule }, dir, null, StaticK.ulimit);
			ThreadPoolExecutor tpe = (ThreadPoolExecutor) Executors.newFixedThreadPool(StaticK.initPoolSize());
			tpe.execute(compile);
			
			while (tpe.getCompletedTaskCount() != 1) {
				try {
					Thread.sleep(1);
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
			tpe.shutdown();
			
			output = compile.getOutput();
			error = compile.getError();
			exitCode = compile.getExitValue();
			timedout = compile.getTimedOut();
			time = System.currentTimeMillis() - millis;
			System.out.println(this + " (" + time + " ms).");
		} else {

			String krun = new File(k3jar).getAbsolutePath();
			
			ThreadPoolExecutor tpe;
			for (Program program: programs){
				program.krun = krun;
				tpe  = (ThreadPoolExecutor) Executors.newFixedThreadPool(1);
				tpe.execute(program);
				
				// wait until the program finishes execution
				while (tpe.getCompletedTaskCount() != 1) {
					try {
						Thread.sleep(1);
					} catch (InterruptedException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}
				tpe.shutdown();
			}
			
			String programss = "Testing " + mainFile + " programs:\n";
			for(Program program : programs)
				programss += "Testing " + program + "\n";
			System.out.println(programss);
		}
	}

	@Override
	public String toString() {
		String newfile = dir + StaticK.fileSep + mainFile;
		return "Testing " + newfile.substring(StaticK.kbasedir.length()) + " : "
				+ (isCompiled() == true ? "success" : "failed");
	}

	public boolean isCompiled() {
		if (timedout)
			return false;
		
		return new File(dir + System.getProperty("file.separator")
				+ compiledFile).exists();
	}

	public long getTime() {
		return time;
	}
	
	public String getFile()
	{
		return new File(mainFile).getName();
	}
	
	public String getJenkinsSuiteName()
	{
		String newfile = dir + StaticK.fileSep + mainFile;
		return newfile.substring(StaticK.kbasedir.length()).replaceAll("\\.\\S+$", "");
	}
}
