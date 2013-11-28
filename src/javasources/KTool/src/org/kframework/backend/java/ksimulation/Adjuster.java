package org.kframework.backend.java.ksimulation;

import org.kframework.backend.java.symbolic.JavaSymbolicKRun;
import org.kframework.kil.Term;

public class Adjuster {
	
	private JavaSymbolicKRun impl;
	private JavaSymbolicKRun spec;

	public Adjuster(JavaSymbolicKRun impl,JavaSymbolicKRun spec){
		
		this.impl=impl;
		
		this.spec=spec;
	}
	
	public boolean isSat(Term implElem,Term specElem){
		
		return true;
	}

}