package org.kframework.backend;

import java.io.IOException;

import org.kframework.kil.Definition;

public interface Backend {
	public void run(Definition definition) throws IOException;
	public String getDefaultStep();
}
