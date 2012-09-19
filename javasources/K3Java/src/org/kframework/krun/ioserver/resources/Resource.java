package org.kframework.krun.ioserver.resources;

public abstract class Resource {

	public Resource() {
		super();
	}

	public abstract void close() throws Exception;
	public abstract void sendToInput(String s) throws Exception;
	public abstract String getFromOutput() throws Exception;

}