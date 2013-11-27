package org.kframework.backend.java.ksimulation;

import org.kframework.backend.java.symbolic.JavaSymbolicKRun;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunExecutionException;

public class Waitor extends Thread{
	
	private JavaSymbolicKRun impl;
	private JavaSymbolicKRun spec;
	private Looper child;
	static boolean result = false;
	
	public Waitor(Context implRules,Context specRules,org.kframework.kil.Term implTerm,org.kframework.kil.Term specTerm) throws KRunExecutionException{
		
		this.impl = new JavaSymbolicKRun(implRules);
		this.spec = new JavaSymbolicKRun(specRules);
		child = new Looper(impl,spec,this);
	}
	
	public void run(){
		
		while(true){
			
			try {
				this.wait();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			if(this.result){
				
				System.out.print(true);
				break;
			}
			else if(Thread.activeCount()==1){
				
				System.out.print(false);
				break;
			}
		}
	}

}
