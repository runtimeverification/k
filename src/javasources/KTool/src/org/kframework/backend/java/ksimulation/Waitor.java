package org.kframework.backend.java.ksimulation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

import org.fusesource.jansi.AnsiConsole;
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
	static int threadNumber = 0 ;
	
	private static final ReentrantReadWriteLock readWriteLock = new ReentrantReadWriteLock();
	private static final Lock read = readWriteLock.readLock();
	private static final Lock write = readWriteLock.writeLock();
	
	public static void upThreadNumber(){
		
		write.lock();
		
		try{
			threadNumber++;
		}finally{
			
			write.unlock();
		}
	}
	
	public static void downThreadNumber(){
		
		write.lock();
		
		try{
			threadNumber=threadNumber-1;
		}finally{
			
			write.unlock();
		}
	}
	
	public Waitor(Context implRules,Context specRules,Term implTerm,Term specTerm) throws KRunExecutionException{
		
		this.impl = new JavaSymbolicKRun(implRules);
		this.spec = new JavaSymbolicKRun(specRules);
		this.impl.initialSimulationRewriter();
		this.spec.initialSimulationRewriter();
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
				synchronized(this){
					this.wait();
				}
			} catch (InterruptedException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			if(Waitor.result){
				
				AnsiConsole.out
                .println(true);
				break;
			}
			else {
				
				int temp = 0 ;
				
				read.lock();
				
				try{
					temp = threadNumber;
				}finally{
					
					read.unlock();
				}
				
				if(temp==0){
				
					AnsiConsole.out
                    .println(false);
				break;
				}
			}
		}
	}

}
