import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

public class Executor extends Thread {

	private String[] commands;
	private String dir;
	private String output = "", error = "";
	private int exitValue;
	private String input;
	
	public Executor(String[] commands, String dir, String input) {
		super();
		this.commands = commands;
		this.dir = dir;
		this.input = input;
	}

	@Override
	public void run() {
			try {
				ProcessBuilder pb = new ProcessBuilder(commands);
				pb.directory(new File(dir));
			    exitValue = timedCall(new MyCallable<Integer>(pb.start()) {
			        public Integer call() throws Exception
			        {
			    		
			    		if (input != null && !input.equals(""))
			    		{
			    			OutputStream stream = p.getOutputStream();
			    			stream.write(input.getBytes());
			    			stream.flush();
			    			stream.close();
			    		}
			    		
			    		exitValue = p.waitFor();
			    		BufferedReader br = new BufferedReader(new InputStreamReader(
			    				p.getInputStream()));
			    		String line;
			    		output = "";
			    		while ((line = br.readLine()) != null) {
			    			output += line + "\n";
			    			line = "";
			    		}

			    		br = new BufferedReader(new InputStreamReader(p.getErrorStream()));
			    		line = ""; error = "";
			    		while ((line = br.readLine()) != null) {
			    			error += line + "\n";
			    			line = "";
			    		}

			    		return p.waitFor();
			        }}, StaticK.ulimit, TimeUnit.SECONDS);
			} catch (TimeoutException e) {
			    output = "Timed out";
			    error = "Timed out.";
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (ExecutionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

	}

	public String[] getCommands() {
		return commands;
	}

	public String getOutput() {
		return output;
	}

	public String getError() {
		return error;
	}

	public int getExitValue() {
		return exitValue;
	}
	
	@Override
	public String toString() {
		String commands = "";
		for(String cmd : this.commands)
			commands += cmd + " ";
		
		return "`" + commands.trim() + "` in directory: " + dir;
	}
	
	private static final ExecutorService THREAD_POOL 
    = Executors.newCachedThreadPool();

	private static <T> T timedCall(Callable<T> c, long timeout, TimeUnit timeUnit)
	    throws InterruptedException, ExecutionException, TimeoutException {
			FutureTask<T> task = new FutureTask<T>(c);
		    THREAD_POOL.execute(task);
		    return task.get(timeout, timeUnit);
	}

}

class MyCallable<T> implements Callable<T>
{
	Process p;
	
	public MyCallable(Process p1)
	{
		this.p = p1;
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public T call() throws Exception {
        return (T) (Integer)p.waitFor();	
	}
}
