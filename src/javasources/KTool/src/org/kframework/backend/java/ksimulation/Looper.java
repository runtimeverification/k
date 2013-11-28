package org.kframework.backend.java.ksimulation;

import java.util.ArrayList;
import java.util.HashSet;

import org.kframework.backend.java.symbolic.*;
import org.kframework.krun.KRunExecutionException;
import org.kframework.kil.Term;

public class Looper extends Thread {
	
	private JavaSymbolicKRun impl;
	private JavaSymbolicKRun spec;
	private HashSet<Term []> memoing;
	private ArrayList<Term []> currentPairs;
	private Waitor refs;
	private Adjuster decider;
	
	public Looper(JavaSymbolicKRun implRules,JavaSymbolicKRun specRules,
			ArrayList<Term []> pairs,HashSet<Term []> memo,Adjuster decider,Waitor father){

		impl = implRules;
		spec = specRules;
		memoing = memo;
		currentPairs = pairs;
		refs = father;
		this.decider=decider;
		
	}
	

	public void run(){
		
		ArrayList<ArrayList<Term []>> result = new ArrayList<ArrayList<Term []>>();
		ArrayList<ArrayList<Term []>> temp = new ArrayList<ArrayList<Term []>>();
		
		for(int i=0;i<this.currentPairs.size();++i){
			
			try {
				temp = getNextMoves(this.currentPairs.get(i));
			} catch (KRunExecutionException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
			if(temp==null){
				
				Waitor.downThreadNumber();
				refs.notify();
				return;
			}
			
			result=this.filter(result, temp);
		}
		
		if(result.isEmpty()){
			
			Waitor.result=true;
			refs.notify();
			return;
		}
		
		if(!Waitor.result){
			
			for(int i=0;i<result.size();++i){
				
				HashSet<Term []> newMemo = new HashSet<Term []>();
				newMemo.addAll(memoing);
				newMemo.addAll(joinAllList(result));
				Looper child = new Looper(impl,spec,result.get(i),newMemo,decider,refs);
				Waitor.upThreadNumber();
				child.start();
			}
		}
	}
	
	public HashSet<Term []> joinAllList(ArrayList<ArrayList<Term []>> input){
		
		HashSet<Term []> temp = new HashSet<Term []>();
		
		for(int i=0;i<input.size();++i){
			
			temp.addAll(input.get(i));
		}
		
		return temp;
	}
	
	private ArrayList<ArrayList<Term []>> getNextMoves(Term [] input) throws KRunExecutionException{
		
		ArrayList<Term> implResult = impl.steps(input[0]);
		ArrayList<Term> specResult = spec.steps(input[1]);
		ArrayList<Term> newImpls = new ArrayList<Term>();
		ArrayList<ArrayList<Term []>> result = new ArrayList<ArrayList<Term []>>();
		
		if(specResult.isEmpty() && !implResult.isEmpty()){
			
			return null;
		}
		
		
		for(int i=0;i<implResult.size();++i){
			
			if(!testMemoing(implResult.get(i),specResult)){
				newImpls.add(implResult.get(i));
			}
		}
		
		for(int i=0;i<newImpls.size();++i){
			
			ArrayList<Term []> temp = useDeciders(newImpls.get(i),specResult);
			
			if (temp.isEmpty()){
				
				return null;
			}
			result=filterAll(temp,result);
		}
		
		return result;

	}
	
	
	private ArrayList<Term []> useDeciders(Term impl,ArrayList<Term> specs){
		
		ArrayList<Term []> temp = new ArrayList<Term []>();
		
		for(int i=0;i<specs.size();++i){
			
			if(decider.isSat(impl, specs.get(i))){
				
				Term [] tempList = new Term[2];
				tempList[0] = impl;
				tempList[1] = specs.get(i);
				temp.add(tempList);
			}
		}
		
		return temp;
	}
	
	private boolean testMemoing(Term impl,ArrayList<Term> specs){
		
		boolean result = false;
		
		Term [] temp = new Term[2];
		
		temp[0] = impl;
		
		for(int i=0;i<specs.size();++i){
			
			temp[1]=specs.get(i);
			
			result = this.memoing.contains(temp);
			
		}
		
		return result;
	}
	
	public ArrayList<ArrayList<Term []>> filterAll(ArrayList<Term []> elems,ArrayList<ArrayList<Term []>> list){
		
		if(list.isEmpty()){
			
			for(int i=0;i<elems.size();++i){
				
				ArrayList<Term []> newElem = new ArrayList<Term []>();
				newElem.add(elems.get(i));
				list.add(newElem);
			}
			
			return list;
		}
		
		ArrayList<ArrayList<Term []>> result = new ArrayList<ArrayList<Term []>>();
		
		for(int i=0;i<elems.size();++i){
			
			ArrayList<ArrayList<Term []>> temp = addElemToAll(elems.get(i),list);
			
			result.addAll(temp);
		}
		
		return result;
	}
	
	
	public ArrayList<ArrayList<Term []>> addElemToAll(Term [] elem,ArrayList<ArrayList<Term []>> list){
		
		ArrayList<ArrayList<Term []>> temp =new ArrayList<ArrayList<Term []>>();
		
		for(int i = 0;i<list.size();++i){
			
			ArrayList<Term []> newElem = new ArrayList<Term []>();
			newElem.addAll(list.get(i));
			newElem.add(elem);	
			temp.add(newElem);
		}
		
		return temp;
	}
	
	
	public ArrayList<ArrayList<Term []>> filter(ArrayList<ArrayList<Term []>> left,ArrayList<ArrayList<Term []>> right){
		
		if(left.isEmpty()){
			
			return right;
		}
		else if(right.isEmpty()){
			
			return left;
		}
		
		ArrayList<ArrayList<Term []>> temp =new ArrayList<ArrayList<Term []>>();
		
		for(int i=0;i<left.size();++i){
			
			for(int j=0;j<right.size();++j){
				
				ArrayList<Term []> newElem = new ArrayList<Term []>();
				
				newElem.addAll(left.get(i));
				newElem.addAll(right.get(j));
				temp.add(newElem);
			}
		}
		
		return temp;	
	}
}