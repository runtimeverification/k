// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.ksimulation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

import org.kframework.backend.java.symbolic.JavaSymbolicKRun;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Spec;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

import com.google.inject.Inject;
import com.google.inject.Provider;

public class Waitor extends Thread{

    private final JavaSymbolicKRun impl;
    private final JavaSymbolicKRun spec;
    private final Provider<org.kframework.kil.Term> implTerm;
    private final Provider<org.kframework.kil.Term> specTerm;
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

    @Inject
    Waitor(
            @Main JavaSymbolicKRun impl,
            @Spec JavaSymbolicKRun spec,
            @Main Provider<org.kframework.kil.Term> implTerm,
            @Spec Provider<org.kframework.kil.Term> specTerm) throws KRunExecutionException{

        this.impl = impl;
        this.spec = spec;
        this.implTerm = implTerm;
        this.specTerm = specTerm;
    }

    public void init() {

        this.impl.initialSimulationRewriter();
        this.spec.initialSimulationRewriter();
        decider = new Adjuster(impl,this.spec);
        ConstrainedTerm [] pair = new ConstrainedTerm[2];


        Term term = Term.of(implTerm.get(), impl.getDefinition());
        GlobalContext globalContext = new GlobalContext(impl.getDefinition(), new PortableFileSystem());
        TermContext termContext0 = TermContext.of(globalContext);
        ConstrainedTerm implConstraint = new ConstrainedTerm(term, termContext0);
        pair[0] = implConstraint;

        term = Term.of(specTerm.get(), this.spec.getDefinition());
        TermContext termContext1 = TermContext.of(globalContext);
        ConstrainedTerm specConstraint = new ConstrainedTerm(term, termContext1);
        pair[1] = specConstraint;


        HashSet<ConstrainedTerm []> memo = new HashSet<ConstrainedTerm[]>();
        ArrayList<ConstrainedTerm []> pairs = new ArrayList<ConstrainedTerm []>();
        pairs.add(pair);

        child = new Looper(impl,this.spec,pairs,memo,decider,this);
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

                System.out.println(true);
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

                if(temp<=0){

                    System.out.println(false);
                break;
                }
            }
        }
    }

}
