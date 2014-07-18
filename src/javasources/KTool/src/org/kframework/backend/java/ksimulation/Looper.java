// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.ksimulation;

import java.util.ArrayList;
import java.util.HashSet;

import org.kframework.backend.java.symbolic.*;
import org.kframework.krun.KRunExecutionException;
import org.kframework.backend.java.kil.ConstrainedTerm;
import com.microsoft.z3.Z3Exception;

public class Looper extends Thread {

    private JavaSymbolicKRun impl;
    private JavaSymbolicKRun spec;
    private HashSet<ConstrainedTerm []> memoing;
    private ArrayList<ConstrainedTerm []> currentPairs;
    private Waitor refs;
    private Adjuster decider;

    public Looper(JavaSymbolicKRun implRules,JavaSymbolicKRun specRules,
            ArrayList<ConstrainedTerm []> pairs,HashSet<ConstrainedTerm []> memo,Adjuster decider,Waitor father){

        impl = implRules;
        spec = specRules;
        memoing = memo;
        currentPairs = pairs;
        refs = father;
        this.decider=decider;

    }


    public void run(){

        Waitor.upThreadNumber();
        ArrayList<ArrayList<ConstrainedTerm []>> result = new ArrayList<ArrayList<ConstrainedTerm []>>();
        ArrayList<ArrayList<ConstrainedTerm []>> temp = null;

        for(int i=0;i<this.currentPairs.size();++i){

            try {
                temp = getNextMoves(this.currentPairs.get(i));
            } catch (KRunExecutionException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            } catch (Z3Exception e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }

            if(temp==null){

                Waitor.downThreadNumber();
                synchronized(refs){
                    refs.notify();
                }
                return;
            }

            result=this.filter(result, temp);
        }

        if(result.isEmpty()){

            Waitor.result=true;
            synchronized(refs){
                refs.notify();
            }
            return;
        }



        if(!Waitor.result){

            for(int i=0;i<result.size();++i){

                HashSet<ConstrainedTerm []> newMemo = new HashSet<ConstrainedTerm []>();
                newMemo.addAll(memoing);

                newMemo.addAll(joinAllList(result));

                Looper child = new Looper(impl,spec,result.get(i),newMemo,decider,refs);


                child.start();
            }
            Waitor.downThreadNumber();
        }
    }



    public HashSet<ConstrainedTerm []> joinAllList(ArrayList<ArrayList<ConstrainedTerm []>> input){

        HashSet<ConstrainedTerm []> temp = new HashSet<ConstrainedTerm []>();

        for(int i=0;i<input.size();++i){

            temp.addAll(input.get(i));
        }

        return temp;
    }

    private ArrayList<ArrayList<ConstrainedTerm []>> getNextMoves(ConstrainedTerm [] input) throws KRunExecutionException, Z3Exception{


        ArrayList<ConstrainedTerm> implResult = impl.steps(input[0]);
        ArrayList<ConstrainedTerm> specResult = spec.steps(input[1]);
        ArrayList<ConstrainedTerm> newImpls = new ArrayList<ConstrainedTerm>();
        ArrayList<ArrayList<ConstrainedTerm []>> result = new ArrayList<ArrayList<ConstrainedTerm []>>();

        if(specResult.isEmpty() && !implResult.isEmpty()){

            return null;
        }

        for(int i=0;i<implResult.size();++i){

            if(!testMemoing(implResult.get(i),specResult)){
                newImpls.add(implResult.get(i));
            }
        }

        for(int i=0;i<newImpls.size();++i){

            ArrayList<ConstrainedTerm []> temp = useDeciders(newImpls.get(i),specResult);

            if (temp.isEmpty()){

                return null;
            }
            result=filterAll(temp,result);
        }

        return result;

    }


    private ArrayList<ConstrainedTerm []> useDeciders(ConstrainedTerm impl,ArrayList<ConstrainedTerm> specs) throws KRunExecutionException, Z3Exception{

        ArrayList<ConstrainedTerm []> temp = new ArrayList<ConstrainedTerm []>();

        for(int i=0;i<specs.size();++i){

            if(decider.isSat(impl, specs.get(i))){

                ConstrainedTerm [] tempList = new ConstrainedTerm[2];
                tempList[0] = impl;
                tempList[1] = specs.get(i);
                temp.add(tempList);
            }
        }

        return temp;
    }

    private boolean testMemoing(ConstrainedTerm impl,ArrayList<ConstrainedTerm> specs){

        boolean result = false;

        ConstrainedTerm [] temp = new ConstrainedTerm[2];

        temp[0] = impl;

        for(int i=0;i<specs.size();++i){

            temp[1]=specs.get(i);

            result = result || this.memoing.contains(temp);

        }

        return result;
    }

    public ArrayList<ArrayList<ConstrainedTerm []>> filterAll(ArrayList<ConstrainedTerm []> elems,ArrayList<ArrayList<ConstrainedTerm []>> list){

        if(list.isEmpty()){

            for(int i=0;i<elems.size();++i){

                ArrayList<ConstrainedTerm []> newElem = new ArrayList<ConstrainedTerm []>();
                newElem.add(elems.get(i));
                list.add(newElem);
            }

            return list;
        }

        ArrayList<ArrayList<ConstrainedTerm []>> result = new ArrayList<ArrayList<ConstrainedTerm []>>();

        for(int i=0;i<elems.size();++i){

            ArrayList<ArrayList<ConstrainedTerm []>> temp = addElemToAll(elems.get(i),list);

            result.addAll(temp);
        }

        return result;
    }


    public ArrayList<ArrayList<ConstrainedTerm []>> addElemToAll(ConstrainedTerm [] elem,ArrayList<ArrayList<ConstrainedTerm []>> list){

        ArrayList<ArrayList<ConstrainedTerm []>> temp =new ArrayList<ArrayList<ConstrainedTerm []>>();

        for(int i = 0;i<list.size();++i){

            ArrayList<ConstrainedTerm []> newElem = new ArrayList<ConstrainedTerm []>();
            newElem.addAll(list.get(i));
            newElem.add(elem);
            temp.add(newElem);
        }

        return temp;
    }


    public ArrayList<ArrayList<ConstrainedTerm []>> filter(ArrayList<ArrayList<ConstrainedTerm []>> left,ArrayList<ArrayList<ConstrainedTerm []>> right){

        if(left.isEmpty()){

            return right;
        }
        else if(right.isEmpty()){

            return left;
        }

        ArrayList<ArrayList<ConstrainedTerm []>> temp =new ArrayList<ArrayList<ConstrainedTerm []>>();

        for(int i=0;i<left.size();++i){

            for(int j=0;j<right.size();++j){

                ArrayList<ConstrainedTerm []> newElem = new ArrayList<ConstrainedTerm []>();

                newElem.addAll(left.get(i));
                newElem.addAll(right.get(j));
                temp.add(newElem);
            }
        }

        return temp;
    }
}