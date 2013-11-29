package org.kframework.backend.java.ksimulation;

import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.symbolic.JavaSymbolicKRun;
import org.kframework.kil.Term;
import org.kframework.krun.KRunExecutionException;

public class Adjuster {
	
	private JavaSymbolicKRun impl;
	private JavaSymbolicKRun spec;

	public Adjuster(JavaSymbolicKRun impl,JavaSymbolicKRun spec){
		
		this.impl=impl;
		
		this.spec=spec;
	}
	
	public boolean isSat(Term implElem,Term specElem) throws KRunExecutionException{
		
		if(impl.getSimulationRewriter().getSimulationMap().isEmpty() 
				|| spec.getSimulationRewriter().getSimulationMap().isEmpty()){
			
			return true;
		}
		
		ConstrainedTerm implside = impl.simulationSteps(implElem);
		ConstrainedTerm specside = spec.simulationSteps(specElem);
		
		if(specside == null){
			
			return true;
		}
		
		if(implside==null){
			return false;
		}
		
		if(implside.equals(specside)){
		return true;
		}
		
		return false;
	}

}