package runner;

import java.io.IOException;

import client.Client;

import main.Main;
import tasks.MaudeTask;
import tasks.Task;

public class KRunner {

	private String maudeCommand = "maude";
	String maudeFile;
		
	public KRunner(String string) {
		maudeFile = string;
	}

	public void run() throws Exception
	{
		// run maude
		Task maude = new MaudeTask(maudeCommand, maudeFile);
		
		new Thread() { public void run() {
		try {
			Main.main(new String[] {"10000"});
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		}}.start();
		
		Client.main(null);
		
		System.out.println("------------- Maude process started -----------------------\n");
		maude.start();
		maude.join();
		System.out.println("\n------------- Maude process finished ----------------------");
		
		System.exit(0);
	}
	
	public static void main(String[] args) {
		if (args.length == 0) {
			System.out.println("Please invoke with the maude file you want to execute as an argument.");
			return;
		}
		KRunner runner = new KRunner(args[0]);
		try {
			runner.run();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
}
