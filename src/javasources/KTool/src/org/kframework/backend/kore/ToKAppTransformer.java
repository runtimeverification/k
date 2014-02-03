package org.kframework.backend.kore;

import java.util.ArrayList;
import java.util.HashMap;

import org.kframework.kil.ASTNode;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.ListBuiltin;
import org.kframework.kil.ListLookup;
import org.kframework.kil.ListUpdate;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.MapLookup;
import org.kframework.kil.MapUpdate;
import org.kframework.kil.SetBuiltin;
import org.kframework.kil.SetLookup;
import org.kframework.kil.SetUpdate;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/*
 * 
 * this Class will translate kil components to KLabel Form
 * 
 */
public class ToKAppTransformer extends CopyOnWriteTransformer {

	public ToKAppTransformer(String name, Context context) {
		super(name, context);
	}
	
    public ToKAppTransformer(Context context) {
        super("Transform NEW into KAPP", context);
    }
	
	@Override
	public ASTNode transform(SetLookup node) throws TransformerException{
		
		ArrayList<Term> temp = new ArrayList<Term>();
		temp.add((Term) node.base().accept(this));
		temp.add((Term)node.key().accept(this));
		temp.add((Term)node.value().accept(this));
		
		return new KApp(new KLabelConstant("Set:lookup"),new KList(temp));
	}
	
	@Override
	public ASTNode transform(ListLookup node) throws TransformerException{
		
		ArrayList<Term> temp = new ArrayList<Term>();
		temp.add((Term) node.base().accept(this));
		temp.add((Term)node.key().accept(this));
		temp.add((Term)node.value().accept(this));
		
		return new KApp(new KLabelConstant("List:lookup"),new KList(temp));
	}
	
	@Override
	public ASTNode transform(MapLookup node) throws TransformerException{
		
		ArrayList<Term> temp = new ArrayList<Term>();
		temp.add((Term) node.base().accept(this));
		temp.add((Term)node.key().accept(this));
		temp.add((Term)node.value().accept(this));
		
		return new KApp(new KLabelConstant("Map:lookup"),new KList(temp));
	}
	
	@Override
	public ASTNode transform(SetUpdate node) throws TransformerException{
		
		ArrayList<Term> temp = new ArrayList<Term>(node.removeEntries());
		for(int i = 0; i < temp.size(); ++i){
			
			temp.set(i,(Term) temp.get(i).accept(this));
		}				
		KList newTerm = new KList(temp);
		
		ArrayList<Term> termSeq = new ArrayList<Term>();
		termSeq.add(newTerm);
		KSequence newEntryTerm = new KSequence(termSeq);
        ArrayList<Term> newArg = new ArrayList<Term>();
        newArg.add((Term) node.set().accept(this));
        newArg.add(newEntryTerm);
		
		return new KApp(new KLabelConstant("Set:update"),new KList(newArg));
	}
	
	@Override
	public ASTNode transform(ListUpdate node) throws TransformerException{
		
		ArrayList<Term> tempLeft = new ArrayList<Term>(node.removeLeft());
		for(int i = 0; i < tempLeft.size(); ++i){
			
			tempLeft.set(i,(Term) tempLeft.get(i).accept(this));
		}
		
		ArrayList<Term> tempRight = new ArrayList<Term>(node.removeRight());
		for(int i = 0; i < tempRight.size(); ++i){
			
			tempRight.set(i,(Term) tempRight.get(i).accept(this));
		}
	
		KList newLeftList = new KList(tempLeft);
		
		KList newRightList = new KList(tempRight);
		
		ArrayList<Term> newLeftSeq = new ArrayList<Term>();
		newLeftSeq.add(newLeftList);
		ArrayList<Term> newRightSeq = new ArrayList<Term>();
		newRightSeq.add(newRightList);
		KSequence newLeftTerm = new KSequence(newLeftSeq);
		KSequence newRightTerm = new KSequence(newRightSeq);
        ArrayList<Term> newArg = new ArrayList<Term>();
        newArg.add((Term) node.base().accept(this));
        newArg.add(newLeftTerm);
        newArg.add(newRightTerm);
		
		return new KApp(new KLabelConstant("List:update"),new KList(newArg));
	}
	
	@Override
	public ASTNode transform(MapUpdate node) throws TransformerException{
		
		
		HashMap<Term,Term> removeMap = new HashMap<Term,Term>(node.removeEntries());
		ArrayList<Term> removeList = new ArrayList<Term>();
		
		for (java.util.Map.Entry<Term, Term> entry : removeMap.entrySet()) {
			
			ArrayList<Term> tempList = new ArrayList<Term>();
			tempList.add((Term) entry.getKey().accept(this));
			tempList.add((Term) entry.getValue().accept(this));

			KApp temp = new KApp(new KLabelConstant(DataStructureSort.DEFAULT_MAP_ITEM_LABEL),new KList(tempList));
			removeList.add(temp);
		}
		
		HashMap<Term,Term> updateMap = new HashMap<Term,Term>(node.updateEntries());
		ArrayList<Term> updateList = new ArrayList<Term>();
		
		for (java.util.Map.Entry<Term, Term> entry : updateMap.entrySet()) {
			
			ArrayList<Term> tempList = new ArrayList<Term>();
			tempList.add((Term) entry.getKey().accept(this));
			tempList.add((Term) entry.getValue().accept(this));

			KApp temp = new KApp(new KLabelConstant(DataStructureSort.DEFAULT_MAP_ITEM_LABEL),new KList(tempList));
			updateList.add(temp);
		}
	
		KList newLeftList = new KList(removeList);
		
		KList newRightList = new KList(updateList);
		
		ArrayList<Term> newLeftSeq = new ArrayList<Term>();
		newLeftSeq.add(newLeftList);
		ArrayList<Term> newRightSeq = new ArrayList<Term>();
		newRightSeq.add(newRightList);
		KSequence newLeftTerm = new KSequence(newLeftSeq);
		KSequence newRightTerm = new KSequence(newRightSeq);
        ArrayList<Term> newArg = new ArrayList<Term>();
        newArg.add((Term) node.map().accept(this));
        newArg.add(newLeftTerm);
        newArg.add(newRightTerm);
		
		return new KApp(new KLabelConstant("Map:update"),new KList(newArg));
	}
	
	@Override
	public ASTNode transform(SetBuiltin node) throws TransformerException{
		
		ArrayList<Term> tempBase = new ArrayList<Term>(node.baseTerms());
		for(int i = 0; i < tempBase.size(); ++i){
			
			tempBase.set(i,(Term) tempBase.get(i).accept(this));
		}
		ArrayList<Term> tempElem = new ArrayList<Term>(node.elements());
		
		for(int i = 0; i < tempElem.size(); ++i){
			
			tempElem.set(i, new KApp(new KLabelConstant(DataStructureSort.DEFAULT_SET_ITEM_LABEL)
			,(Term)tempElem.get(i).accept(this)));
		}
		
		tempBase.addAll(tempElem);
		
		if(tempBase.size()==0){
			
			return new KLabelConstant(DataStructureSort.DEFAULT_SET_UNIT_LABEL);
		}
		
		ArrayList<Term> basedTerm = new ArrayList<Term>();
		basedTerm.add(tempBase.get(tempBase.size()-1));
		basedTerm.add(new KLabelConstant(DataStructureSort.DEFAULT_SET_UNIT_LABEL));
		KApp basedKapp = new KApp(new KLabelConstant(DataStructureSort.DEFAULT_SET_LABEL),new KList(basedTerm));
		
		for(int i = tempBase.size()-2; i >= 0; --i){
			
			ArrayList<Term> tempTerm = new ArrayList<Term>();
			tempTerm.add(tempBase.get(i));
			tempTerm.add(basedKapp);
			basedKapp = new KApp(new KLabelConstant(DataStructureSort.DEFAULT_SET_LABEL),new KList(tempTerm));
		}
		
		return basedKapp;
	}
	
	/*
	 * a helper function to parse all baseterm in ListBultin into a list of terms
	 * which are translated into k-label form
	 */
	private ArrayList<Term> getAllTermsInBase(ArrayList<Term> base) throws TransformerException{
		
		ArrayList<Term> result = new ArrayList<Term>();
		for(int i = 0; i < base.size(); ++i){
			if(base.get(i) instanceof ListBuiltin){
				
				ListBuiltin temp = (ListBuiltin) base.get(i);
				ArrayList<Term> tempLeft = new ArrayList<Term>(temp.elementsLeft());
				for(int j = 0; j < tempLeft.size(); ++j){
					
					result.add(new KApp(new KLabelConstant(DataStructureSort.DEFAULT_LIST_ITEM_LABEL)
					,(Term)tempLeft.get(i).accept(this)));
				}
				ArrayList<Term> tempMidTerms = new ArrayList<Term>(temp.baseTerms());
				ArrayList<Term> tempBase = getAllTermsInBase(tempMidTerms);
				
				result.addAll(tempBase);
				
				ArrayList<Term> tempRight = new ArrayList<Term>(temp.elementsRight());
				for(int j = 0; j < tempRight.size(); ++j){
					
					result.add(new KApp(new KLabelConstant(DataStructureSort.DEFAULT_LIST_ITEM_LABEL)
					,(Term)tempRight.get(i).accept(this)));
				}
				
			} else{
				
				result.add((Term) base.get(i).accept(this));
			}
		}
		
		return result;
	}
	
	@Override
	public ASTNode transform(ListBuiltin node) throws TransformerException{
		
		ArrayList<Term> tempBase = new ArrayList<Term>(node.baseTerms());
		tempBase = getAllTermsInBase(tempBase);
		ArrayList<Term> tempElem = new ArrayList<Term>(node.elementsLeft());
		
		for(int i = 0; i < tempElem.size(); ++i){
			
			tempElem.set(i, new KApp(new KLabelConstant(DataStructureSort.DEFAULT_LIST_ITEM_LABEL)
			,(Term)tempElem.get(i).accept(this)));
		}
		
		tempElem.addAll(tempBase);
		
		ArrayList<Term> tempElemRight = new ArrayList<Term>(node.elementsRight());
		
		for(int i = 0; i < tempElemRight.size(); ++i){
			
			tempElemRight.set(i, new KApp(new KLabelConstant(DataStructureSort.DEFAULT_LIST_ITEM_LABEL)
			,(Term)tempElemRight.get(i).accept(this)));
		}
		
		tempElem.addAll(tempElemRight);
		
		if(tempElem.size()==0){
			
			return new KLabelConstant(DataStructureSort.DEFAULT_LIST_UNIT_LABEL);
		}
		
		ArrayList<Term> basedTerm = new ArrayList<Term>();
		basedTerm.add(tempElem.get(tempElem.size()-1));
		basedTerm.add(new KLabelConstant(DataStructureSort.DEFAULT_LIST_UNIT_LABEL));
		KApp basedKapp = new KApp(new KLabelConstant(DataStructureSort.DEFAULT_LIST_LABEL),new KList(basedTerm));
		
		for(int i = tempElem.size()-2; i >= 0; --i){
			
			ArrayList<Term> tempTerm = new ArrayList<Term>();
			tempTerm.add(tempElem.get(i));
			tempTerm.add(basedKapp);
			basedKapp = new KApp(new KLabelConstant(DataStructureSort.DEFAULT_LIST_LABEL),new KList(tempTerm));
		}
		
		return basedKapp;
	}
	
	@Override
	public ASTNode transform(MapBuiltin node) throws TransformerException{
		
		ArrayList<Term> tempBase = new ArrayList<Term>(node.baseTerms());
		for(int i = 0; i < tempBase.size(); ++i){
			
			tempBase.set(i,(Term) tempBase.get(i).accept(this));
		}
		
		ArrayList<Term> updateList = new ArrayList<Term>();
		
		for (java.util.Map.Entry<Term, Term> entry : node.elements().entrySet()) {
			
			ArrayList<Term> tempList = new ArrayList<Term>();
			tempList.add((Term) entry.getKey().accept(this));
			tempList.add((Term) entry.getValue().accept(this));

			KApp temp = new KApp(new KLabelConstant(DataStructureSort.DEFAULT_MAP_ITEM_LABEL),new KList(tempList));
			updateList.add(temp);
		}
		
		tempBase.addAll(updateList);
		
		if(tempBase.size()==0){
			
			return new KLabelConstant(DataStructureSort.DEFAULT_MAP_UNIT_LABEL);
		}
		
		ArrayList<Term> basedTerm = new ArrayList<Term>();
		basedTerm.add(tempBase.get(tempBase.size()-1));
		basedTerm.add(new KLabelConstant(DataStructureSort.DEFAULT_MAP_UNIT_LABEL));
		KApp basedKapp = new KApp(new KLabelConstant(DataStructureSort.DEFAULT_MAP_LABEL),new KList(basedTerm));
		
		for(int i = tempBase.size()-2; i >= 0; --i){
			
			ArrayList<Term> tempTerm = new ArrayList<Term>();
			tempTerm.add(tempBase.get(i));
			tempTerm.add(basedKapp);
			basedKapp = new KApp(new KLabelConstant(DataStructureSort.DEFAULT_MAP_LABEL),new KList(tempTerm));
		}
		
		return basedKapp;
	}
	
}
