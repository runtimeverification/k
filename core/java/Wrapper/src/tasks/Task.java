package tasks;

public abstract class Task extends Thread {
	
	protected String cmd;

	public Task(String cmd) {

		this.cmd = cmd;
	}
}
