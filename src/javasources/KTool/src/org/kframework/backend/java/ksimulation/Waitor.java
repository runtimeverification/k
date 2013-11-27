package org.kframework.backend.java.ksimulation;

import java.util.ArrayList;
import java.util.HashSet;

import org.kframework.backend.java.symbolic.JavaSymbolicKRun;
import org.kframework.kil.loader.Context;
import org.kframework.krun.KRunExecutionException;
import org.kframework.kil.Term;

public class Waitor extends Thread{
	
	private JavaSymbolicKRun impl;
	private JavaSymbolicKRun spec;
	private Looper child;
	private Adjuster decider;
	static boolean result = false;
	
	public Waitor(Context implRules,Context specRules,Term implTerm,Term specTerm) throws KRunExecutionException{
		
		this.impl = new JavaSymbolicKRun(implRules);
		this.spec = new JavaSymbolicKRun(specRules);
		decider = new Adjuster(impl,spec);
		Term [] pair = new Term[2];
		pair[0] = implTerm;
		pair[1] = specTerm;
		HashSet<Term []> memo = new HashSet<Term[]>();
		ArrayList<Term []> pairs = new ArrayList<Term []>();
		pairs.add(pair);
		
		child = new Looper(impl,spec,pairs,memo,decider,this);
	}
	
	public void run(){
		
		child.start();
		
		while(true){
			
			try {
				this.wait();
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			if(Waitor.result){
				
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
