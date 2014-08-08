// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.ksimulation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

import org.kframework.backend.java.symbolic.SymbolicRewriter;
import org.kframework.krun.KRunExecutionException;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Spec;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.KilFactory;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

import com.google.inject.Inject;
import com.google.inject.Provider;

public class Waitor extends Thread{

    private final SymbolicRewriter impl, spec;
    private final Provider<org.kframework.kil.Term> implTerm, specTerm;
    private final Provider<GlobalContext> implGlobalContext, specGlobalContext;
    private final KilFactory implFactory, specFactory;
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
            @Main SymbolicRewriter impl,
            @Spec SymbolicRewriter spec,
            @Main Provider<org.kframework.kil.Term> implTerm,
            @Spec Provider<org.kframework.kil.Term> specTerm,
            @Main Provider<GlobalContext> implGlobalContext,
            @Spec Provider<GlobalContext> specGlobalContext,
            @Main KilFactory implFactory,
            @Spec KilFactory specFactory) throws KRunExecutionException{

        this.impl = impl;
        this.spec = spec;
        this.implTerm = implTerm;
        this.specTerm = specTerm;
        this.implFactory = implFactory;
        this.specFactory = specFactory;
        this.implGlobalContext = implGlobalContext;
        this.specGlobalContext = specGlobalContext;
    }

    public void init() {

        decider = new Adjuster(impl,this.spec);
        ConstrainedTerm [] pair = new ConstrainedTerm[2];


        Term term = implFactory.term(implTerm.get());
        ConstrainedTerm implConstraint = new ConstrainedTerm(term, TermContext.of(implGlobalContext.get()));
        pair[0] = implConstraint;

        term = specFactory.term(specTerm.get());
        ConstrainedTerm specConstraint = new ConstrainedTerm(term, TermContext.of(specGlobalContext.get()));
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
