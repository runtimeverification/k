package org.kframework.kil.visitors;

import java.util.ArrayList;
import java.util.HashMap;

import org.kframework.kil.*;
import org.kframework.kil.matchers.MapInsertPattern;
import org.kframework.kil.matchers.MapLookupPattern;
import org.kframework.kil.matchers.SetInsertPattern;
import org.kframework.kil.matchers.SetLookupPattern;
import org.kframework.kil.rewriter.MapImpl;
import org.kframework.kil.rewriter.SetImpl;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class KilTransformer {
	
	
	public static KSequence kseqWrap(KApp item){
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		tempList.add(item);
		
		return new KSequence(tempList);
	}
	
	/*
	 * Liyi Li
	 * input either KList KItem K or KLabel and return the wraping KSequence
	 * 
	 */
	public static KSequence kseqAdjust(Term item){
		
		if(item instanceof KList){
			KApp temp = new KApp(new KLabelConstant("List"),item);
			return kseqWrap(temp);
		} else if (item instanceof KSequence) {
			return (KSequence) item;
		} else if (item instanceof KApp) {
			return kseqWrap((KApp) item);
		} else if (item instanceof KLabel) {
			return kseqWrap(kappWrap((KLabel) item));
		} else if ((item instanceof Bag) || (item instanceof Cell)) {
			ArrayList<Term> tempList = new ArrayList<Term>();
			tempList.add(item);
			return new KSequence(tempList);
		} else {
			return null;
		}
	}
	
	/*
	 * Liyi Li
	 * input either KList KItem K or KLabel and return the wraping KList
	 * 
	 */
	public static KList kListAdjust(Term item){
		
		if(item instanceof KList){
			return (KList) item;
		} else if (item instanceof KSequence) {
			return kListWrap((KSequence) item);
		} else if (item instanceof KApp) {
			return kListWrap(kseqWrap((KApp) item));
		} else if (item instanceof KLabel) {
			return kListWrap(kseqWrap(kappWrap((KLabel) item)));
		} else if ((item instanceof Bag) || (item instanceof Cell)) {
			ArrayList<Term> tempList = new ArrayList<Term>();
			tempList.add(item);
			return new KList(tempList);
		} else {
			return null;
		}
	}
	
	
	public static KApp kappWrap(KLabel item){
		
		return new KApp(item,new KList());
	}
	
	public static KList kListWrap(KSequence item){
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		tempList.add(item);
		
		return new KList(tempList);
	}
	
	
	public Term kilToKore(Term node) {
		if (node instanceof TermComment){
			
			return this.kilToKore((TermComment)node);
		} else if (node instanceof Cell){
			
			return this.kilToKore((Cell)node);
		} if (node instanceof Ambiguity){
			
			return this.kilToKore((Ambiguity)node);
		} if (node instanceof Bag){
			
			return this.kilToKore((Bag)node);
		} if (node instanceof KSequence){
			
			return this.kilToKore((KSequence)node);
		} if (node instanceof org.kframework.kil.List){
			
			return this.kilToKore((org.kframework.kil.List)node);
		} if (node instanceof KList){
			
			return this.kilToKore((KList)node);
		} if (node instanceof Map){
			
			return this.kilToKore((Map)node);
		} if (node instanceof Set){
			
			return this.kilToKore((Set)node);
		} if (node instanceof BagItem){
			
			return this.kilToKore((BagItem)node);
		} if (node instanceof SetItem){
			
			return this.kilToKore((SetItem)node);
		} if (node instanceof ListItem){
			
			return this.kilToKore((ListItem)node);
		} if (node instanceof MapItem){
			
			return this.kilToKore((MapItem)node);
		} if (node instanceof SetBuiltin){
			
			return this.kilToKore((CollectionBuiltin)node);
		} if (node instanceof SetLookup){
			
			return this.kilToKore((SetLookup)node);
		} if (node instanceof SetUpdate){
			
			return this.kilToKore((SetUpdate)node);
		} if (node instanceof ListBuiltin){
			
			return this.kilToKore((ListBuiltin)node);
		} if (node instanceof ListUpdate){
			
			return this.kilToKore((ListUpdate)node);
		} if ((node instanceof ListLookup) || (node instanceof MapLookup)){
			
			return this.kilToKore((BuiltinLookup)node);
		} if (node instanceof MapBuiltin){
			
			return this.kilToKore((MapBuiltin)node);
		} if (node instanceof MapUpdate){
			
			return this.kilToKore((MapUpdate)node);
		} if (node instanceof Token){
			
			return this.kilToKore((Token)node);
		} if (node instanceof ListTerminator){
			
			return this.kilToKore((ListTerminator)node);
		} if (node instanceof Hole){
			
			return this.kilToKore((Hole)node);
		} if (node instanceof KApp){
			
			return this.kilToKore((KApp)node);
		} if (node instanceof KLabelConstant){
			
			return this.kilToKore((KLabelConstant)node);
		} else if (node instanceof KInjectedLabel){
			
			return this.kilToKore((KInjectedLabel)node);
		} if (node instanceof FreezerHole){
			
			return this.kilToKore((FreezerHole)node);
		} if (node instanceof Rewrite){
			
			return this.kilToKore((Rewrite)node);
		} if (node instanceof TermCons){
			
			return this.kilToKore((TermCons)node);
		} else if (node instanceof Bracket){
			
			return this.kilToKore((Bracket)node);
		} else if (node instanceof Cast){
			
			return this.kilToKore((Cast)node);
		} else if (node instanceof Variable){
			
			return this.kilToKore((Variable)node);
		} else if (node instanceof Freezer){
			
			return this.kilToKore((Freezer)node);
		} else if (node instanceof BackendTerm){
			
			return this.kilToKore((BackendTerm)node);
		} else if (node instanceof MapInsertPattern){
			
			return this.kilToKore((MapInsertPattern)node);
		} else if (node instanceof MapLookupPattern){
			
			return this.kilToKore((MapLookupPattern)node);
		} else if (node instanceof SetInsertPattern){
			
			return this.kilToKore((SetInsertPattern)node);
		} else if (node instanceof SetLookupPattern){
			
			return this.kilToKore((SetLookupPattern)node);
		} else if (node instanceof MapImpl){
			
			return this.kilToKore((MapImpl)node);
		} else if (node instanceof SetImpl){
			
			return this.kilToKore((SetImpl)node);
		} else return null;
	}
	
	public Term kilToKore(Cell node){
		Cell result = new Cell(node);
		result.setContents(this.kilToKore(node.getContents()));
		return result;
	}
	

	public Term kilToKore(TermComment node) {
		return new KLabelConstant("<br />");
	}

	public Term kilToKore(Ambiguity node) {
		
		KLabel tempLabel = new KLabelConstant("amb");
		
		ArrayList<Term> tempList = new ArrayList<Term>(node.getContents());
		
		for(int i=0;i<tempList.size();i++){
			
			KSequence elem = kseqAdjust((this.kilToKore(tempList.get(i))));
			tempList.set(i, elem);
		}
		
		KList resultKList = new KList(tempList);
		
		KApp result = new KApp(tempLabel, resultKList);
		return result;
	}
	
	public Term kilToKore(Bag node){
		
		ArrayList<Term> tempList = new ArrayList<Term>(node.getContents());
		
		for(int i = 0;i< tempList.size();++i){
			tempList.set(i, (Term) this.kilToKore(tempList.get(i)));
		}
		
		return new Bag(tempList);
	}
	
	public Term kilToKore(KSequence node) {
		
		ArrayList<Term> resultList = new ArrayList<Term>();
		
		for(int i=0;i<node.getContents().size();++i){
			
			KSequence temp = kseqAdjust(this.kilToKore(node.getContents().get(i)));
			resultList.addAll(temp.getContents());
		}
		
		return new KSequence(resultList);
	}
	
	public Term kilToKore(org.kframework.kil.List node) {
		
		KLabel tempLabel = new KLabelConstant("List");
		
		ArrayList<Term> tempList = new ArrayList<Term>(node.getContents());
		
		for(int i=0;i<tempList.size();i++){
			
			KSequence elem = kseqAdjust((this.kilToKore(tempList.get(i))));
			tempList.set(i, elem);
		}
		
		KList resultKList = new KList(tempList);
		
		KApp result = new KApp(tempLabel, resultKList);
		return result;
	}
	
	public Term kilToKore(KList node) {
		
		ArrayList<Term> resultList = new ArrayList<Term>();
		for(int i=0;i<node.getContents().size();++i){
			
			KList temp = kListAdjust(this.kilToKore(node.getContents().get(i)));
			resultList.addAll(temp.getContents());
		}
		
		return new KList(resultList);
	}
	
	public Term kilToKore(Map node) {
		
		KLabel tempLabel = new KLabelConstant("Map");
		
		ArrayList<Term> tempList = new java.util.ArrayList<Term>(node.getContents());
		
		for(int i=0;i<tempList.size();i++){
			
			KSequence elem = kseqAdjust(this.kilToKore(tempList.get(i)));
			tempList.set(i, elem);
		}
		
		KList resultKList = new KList(tempList);
		
		KApp result = new KApp(tempLabel, resultKList);
		return result;
	}

	
	public Term kilToKore(Set node) {
		
		KLabel tempLabel = new KLabelConstant("Set");
		
		ArrayList<Term> tempList = new ArrayList<Term>(node.getContents());
		
		for(int i=0;i<tempList.size();i++){
			
			KSequence elem = kseqAdjust(this.kilToKore(tempList.get(i)));
			tempList.set(i, elem);
		}
		
		KList resultKList = new KList(tempList);
		
		KApp result = new KApp(tempLabel, resultKList);
		return result;
	}

	public Term kilToKore(BagItem node) {
		return this.kilToKore(node.getItem());
	}
	

	public Term kilToKore(ListItem node) {
		return this.kilToKore(node.getItem());
	}

	public Term kilToKore(MapItem node) {
		
		KLabel tempLabel = new KLabelConstant("_|->_");
		
		KSequence keyTerm = kseqAdjust(this.kilToKore(node.getKey()));
		KSequence valueTerm = kseqAdjust(this.kilToKore(node.getValue()));
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		tempList.add(keyTerm);
		tempList.add(valueTerm);
		
		KApp result = new KApp(tempLabel, new KList(tempList));
		return result;
	}
	
	public Term kilToKore(SetItem node) {
		return this.kilToKore(node.getItem());
	}
	
	public Term kilToKore(CollectionBuiltin node) {
		
		KLabel tempLabel = new KLabelConstant("CollectionBuiltin");
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		tempList.addAll(node.elements());
		tempList.addAll(node.baseTerms());
		
		for(int i=0;i<tempList.size();i++){
			
			KSequence elem = kseqAdjust((this.kilToKore(tempList.get(i))));
			tempList.set(i, elem);
		}
		
		KList resultKList = new KList(tempList);
		
		KApp result = new KApp(tempLabel, resultKList);
		return result;
	}

	public Term kilToKore(SetLookup node) {
		
		KLabel tempLabel = new KLabelConstant("_(_)");
		
		KSequence nameTerm = kseqAdjust(this.kilToKore(node.base()));
		KSequence keyTerm = kseqAdjust(this.kilToKore(node.key()));
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		tempList.add(nameTerm);
		tempList.add(keyTerm);
		
		KApp result = new KApp(tempLabel, new KList(tempList));
		return result;
	}

	public Term kilToKore(SetUpdate node) {
		
		KLabel tempLabel = new KLabelConstant("setUpdate(_,_)");
		
		ArrayList<Term> updateList = new ArrayList<Term>(node.removeEntries());
		
		for(int i=0;i<updateList.size();++i){
			
			updateList.set(i, kseqAdjust(kilToKore(updateList.get(i))));
		}
		
		KApp updateItem = new KApp(new KLabelConstant("List"),new KList(updateList));
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		tempList.add(kListAdjust(kilToKore(node.set())));
		tempList.add(updateItem);
		
		return new KApp(tempLabel,new KList(tempList));
	}
	
	public Term kilToKore(ListBuiltin node) {
		
		KLabel tempLabel = new KLabelConstant("CollectionBuiltin");
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		tempList.addAll(node.elementsLeft());
		tempList.addAll(node.baseTerms());
		tempList.addAll(node.elementsRight());
		
		for(int i=0;i<tempList.size();i++){
			
			KSequence elem = kseqAdjust((kilToKore(tempList.get(i))));
			tempList.set(i, elem);
		}
		
		KList resultKList = new KList(tempList);
		
		KApp result = new KApp(tempLabel, resultKList);
		return result;
	}
	
	public Term kilToKore(ListUpdate node) {
		
		KLabel tempLabel = new KLabelConstant("_[_/_]");
		
		ArrayList<Term> leftList = new ArrayList<Term>(node.removeLeft());
		ArrayList<Term> rightList = new ArrayList<Term>(node.removeRight());
		
		for(int i=0;i<leftList.size();++i){
			
			leftList.set(i, kseqAdjust(kilToKore(leftList.get(i))));
		}
		
		for(int i=0;i<rightList.size();++i){
			
			rightList.set(i,kseqAdjust(kilToKore(rightList.get(i))));
		}
		
		KApp leftItem = new KApp(new KLabelConstant("List"),new KList(leftList));
		KApp rightItem = new KApp(new KLabelConstant("List"),new KList(rightList));
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		tempList.add(kListAdjust(kilToKore(node.base())));
		tempList.add(leftItem);
		tempList.add(rightItem);
		
		return new KApp(tempLabel,new KList(tempList));
	}
	
	public Term kilToKore(BuiltinLookup node) {
		
		KLabel tempLabel = new KLabelConstant("_(_)->_");
		
		KSequence nameTerm = kseqAdjust(kilToKore(node.base()));
		KSequence keyTerm = kseqAdjust(kilToKore(node.key()));
		KSequence valueTerm = kseqAdjust(kilToKore(node.value()));
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		tempList.add(nameTerm);
		tempList.add(keyTerm);
		tempList.add(valueTerm);
		
		KApp result = new KApp(tempLabel, new KList(tempList));
		return result;
	}
	
	public Term kilToKore(MapBuiltin node) {
		
		KLabel tempLabel = new KLabelConstant("MapBuiltin");
		
		ArrayList<Term> tempList = new java.util.ArrayList<Term>();

		for (java.util.Map.Entry<Term, Term> entry : node.elements().entrySet()) {
			
			KSequence keyTerm = kseqAdjust(kilToKore(entry.getKey()));
			KSequence valueTerm = kseqAdjust(kilToKore(entry.getValue()));
			
			ArrayList<Term> newList = new ArrayList<Term>();
			newList.add(keyTerm);
			newList.add(valueTerm);
			tempList.add(kseqAdjust(new KApp(new KLabelConstant("_|->_"),new KList(newList))));
		}
		
		ArrayList<Term> newList = new ArrayList<Term>(node.baseTerms());
		for(int i=0;i<newList.size();i++){
			
			KSequence elem = kseqAdjust(kilToKore(newList.get(i)));
			tempList.add(elem);
		}
		
		KList resultKList = new KList(tempList);
		
		KApp result = new KApp(tempLabel, resultKList);
		return result;
	}
	
	public Term kilToKore(MapUpdate node) {
		
		KLabel tempLabel = new KLabelConstant("mapUpdate(_,_,_)");
		
		HashMap<Term,Term> removeMap = new HashMap<Term,Term>(node.removeEntries());
		ArrayList<Term> removeList = new ArrayList<Term>();
		
		for (java.util.Map.Entry<Term, Term> entry : removeMap.entrySet()) {
			
			ArrayList<Term> tempList = new ArrayList<Term>();
			tempList.add(kseqAdjust(kilToKore(entry.getKey())));
			tempList.add(kseqAdjust(kilToKore(entry.getValue())));

			KApp temp = new KApp(new KLabelConstant("_|->_"),new KList(tempList));
			removeList.add(kseqAdjust(temp));
		}
		
		HashMap<Term,Term> updateMap = new HashMap<Term,Term>(node.updateEntries());
		ArrayList<Term> updateList = new ArrayList<Term>();
		
		for (java.util.Map.Entry<Term, Term> entry : updateMap.entrySet()) {
			
			ArrayList<Term> tempList = new ArrayList<Term>();
			tempList.add(kseqAdjust(kilToKore(entry.getKey())));
			tempList.add(kseqAdjust(kilToKore(entry.getValue())));

			KApp temp = new KApp(new KLabelConstant("_|->_"),new KList(tempList));
			updateList.add(kseqAdjust(temp));
		}
		
		KApp leftItem = new KApp(new KLabelConstant("List"),new KList(removeList));
		KApp rightItem = new KApp(new KLabelConstant("List"),new KList(updateList));
		
		java.util.List<Term> tempList = new java.util.ArrayList<Term>();
		tempList.add(kListAdjust(kilToKore(node.map())));
		tempList.add(leftItem);
		tempList.add(rightItem);
		
		return new KApp(tempLabel,new KList(tempList));
	}
	
	public Term kilToKore(Token node){
		
		return new KLabelConstant("#token(\"" + node.tokenSort() + "\", "+node.value()+")");
	}
	
	public Term kilToKore(ListTerminator node) {
		if (node.separator() != null && node.getSort().equals(KSorts.K)) {
			return new KLabelConstant(".List{\"" + node.separator() + "\"}");
        } else {
		return new KLabelConstant("." + node.getSort());
		}
	}
	
	public Term kilToKore(Hole node) {
		// TODO Auto-generated method stub
		return new KLabelConstant("HOLE");
	}

	public Term kilToKore(KApp node) {
		
		return new KApp(kilToKore(node.getLabel()),kListAdjust(kilToKore(node.getChild())));
	}
	
	public Term kilToKore(KLabelConstant node) {
		return node;
	}

	public Term kilToKore(KInjectedLabel node) {
		return new KApp(new KLabelConstant(KInjectedLabel.getInjectedSort(node.getSort())+"2Klabel"),kListAdjust(kilToKore(node.getTerm())));
	}


	public Term kilToKore(FreezerHole node) {
		return new KApp(new KLabelConstant("HOLE"),
				kListAdjust(new KLabelConstant(String.valueOf(node.getIndex()))));
	}

	public Term kilToKore(Rewrite node) {
		
		KLabel tempLabel = new KLabelConstant("_=>_");
		
		KSequence keyTerm = kseqAdjust(kilToKore(node.getLeft()));
		KSequence valueTerm = kseqAdjust(kilToKore(node.getRight()));
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		tempList.add(keyTerm);
		tempList.add(valueTerm);
		
		KApp result = new KApp(tempLabel, new KList(tempList));
		return result;
	}
	
	public Term kilToKore(TermCons node) {

		if (node.getProduction().isListDecl()) {
			UserList userList = (UserList) node.getProduction().getItems().get(0);
			String separator = userList.getSeparator();
			ArrayList<Term> contents = new ArrayList<Term>(node.getContents());
			ArrayList<Term> tempList = new ArrayList<Term>();
			tempList.add(kseqAdjust(kilToKore(contents.get(0))));
			tempList.add(kseqAdjust(kilToKore(contents.get(1))));
			return new KApp(new KLabelConstant("_"+separator+"_"),new KList(tempList));
		} else {
			
			ArrayList<Term> tempList = new ArrayList<Term>();
			String label = "";
			int where = 0;
			for (int i = 0; i < node.getProduction().getItems().size(); ++i) {
				ProductionItem productionItem = node.getProduction().getItems().get(i);
				if (!(productionItem instanceof Terminal)) {
					
					KSequence tempK = kseqAdjust(kilToKore(node.getContents().get(where++)));
					tempList.add(tempK);
				} else {
					
					if ( !((Terminal) productionItem).getTerminal().equals("(") 
							&& !((Terminal) productionItem).getTerminal().equals(")")){
						label += ((Terminal) productionItem).getTerminal();
					}
				}
			}
			return new KApp(new KLabelConstant(label),new KList(tempList));
		}
	}

	public Term kilToKore(Bracket node) {
		
		return new KApp(new KLabelConstant("(_)"),kListAdjust(kilToKore(node.getContent())));
	}
	
	public Term kilToKore(Cast node) {
		
		KLabel tempLabel = new KLabelConstant("_::_");
		
		KSequence contentTerm = kseqAdjust(kilToKore(node.getContent()));
		KSequence sortTerm = kseqAdjust(new KLabelConstant(node.getSort()));
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		tempList.add(contentTerm);
		tempList.add(sortTerm);
		
		KApp result = new KApp(tempLabel, new KList(tempList));
		return result;
	}
	
	public Term kilToKore(Variable node) {
		
		if(node.isFresh()){
			return new KLabelConstant("?"+node.getName()+":"+node.getSort());
		} else {
			return new KLabelConstant(node.getName()+":"+node.getSort());
		}
	}

	public Term kilToKore(Freezer node) {
		return kilToKore(node.getTerm());
	}

	public Term kilToKore(BackendTerm node) {
		return new KApp(new KLabelConstant(node.getValue()),new KList());
	}
	
	public Term kilToKore(MapInsertPattern node) {
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		for(int i = 0;i<node.getInsertions().size();++i){
			
			Term tempKey = this.kilToKore(node.getInsertions().get(i).getKey());
			Term tempValue = this.kilToKore(node.getInsertions().get(i).getValue());
			
			ArrayList<Term> mapList = new ArrayList<Term>();
			mapList.add(kseqAdjust(tempKey));
			mapList.add(kseqAdjust(tempValue));
			
			KApp tempNode = new KApp((new KLabelConstant("_|->_")),(new KList(mapList)));
			tempList.add(tempNode);
		}
		
		KSequence firstNode = kseqAdjust(new KList(tempList));
		KLabelConstant secondLabel = null;
		if(node.getRemainder().isFresh()){
			secondLabel = new KLabelConstant("?"+node.getRemainder().getName()+":"+node.getRemainder().getSort());
		} else {
			secondLabel = new KLabelConstant(node.getRemainder().getName()+":"+node.getRemainder().getSort());
		}
		
		ArrayList<Term> resultList = new ArrayList<Term>();
		resultList.add(firstNode);
		resultList.add(kseqAdjust(secondLabel));
		return new KApp(new KLabelConstant("mapInsertPattern(_,_)"),new KList(resultList));
	}
	
	
	public Term kilToKore(MapLookupPattern node) {
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		for(int i = 0;i<node.getLookups().size();++i){
			
			Term tempKey = this.kilToKore(node.getLookups().get(i).getKey());
			Term tempValue = this.kilToKore(node.getLookups().get(i).getValue());
			
			ArrayList<Term> mapList = new ArrayList<Term>();
			mapList.add(kseqAdjust(tempKey));
			mapList.add(kseqAdjust(tempValue));
			
			KApp tempNode = new KApp((new KLabelConstant("_|->_")),(new KList(mapList)));
			tempList.add(tempNode);
		}
		
		KSequence firstNode = kseqAdjust(new KList(tempList));
		KLabelConstant secondLabel = null;
		if(node.getRemainder().isFresh()){
			secondLabel = new KLabelConstant("?"+node.getRemainder().getName()+":"+node.getRemainder().getSort());
		} else {
			secondLabel = new KLabelConstant(node.getRemainder().getName()+":"+node.getRemainder().getSort());
		}
		
		ArrayList<Term> resultList = new ArrayList<Term>();
		resultList.add(firstNode);
		resultList.add(kseqAdjust(secondLabel));
		return new KApp(new KLabelConstant("mapLookUpPattern(_,_)"),new KList(resultList));
	}

	public Term kilToKore(SetInsertPattern node) {
		
		ArrayList<Term> tempList = new ArrayList<Term>(node.getInsertions());
		for(int i = 0;i<tempList.size();++i){
			
			KSequence elem = kseqAdjust(kilToKore(tempList.get(i)));
			tempList.set(i, elem);
		}
		
		KSequence firstNode = kseqAdjust(new KList(tempList));
		KLabelConstant secondLabel = null;
		if(node.getRemainder().isFresh()){
			secondLabel = new KLabelConstant("?"+node.getRemainder().getName()+":"+node.getRemainder().getSort());
		} else {
			secondLabel = new KLabelConstant(node.getRemainder().getName()+":"+node.getRemainder().getSort());
		}
		
		ArrayList<Term> resultList = new ArrayList<Term>();
		resultList.add(firstNode);
		resultList.add(kseqAdjust(secondLabel));
		return new KApp(new KLabelConstant("setInsertPattern(_,_)"),new KList(resultList));
	}
	

	public Term kilToKore(SetLookupPattern node) {
		
		ArrayList<Term> tempList = new ArrayList<Term>(node.getLookups());
		for(int i = 0;i<tempList.size();++i){
			
			KSequence elem = kseqAdjust(kilToKore(tempList.get(i)));
			tempList.set(i, elem);
		}
		
		KSequence firstNode = kseqAdjust(new KList(tempList));
		KLabelConstant secondLabel = null;
		if(node.getRemainder().isFresh()){
			secondLabel = new KLabelConstant("?"+node.getRemainder().getName()+":"+node.getRemainder().getSort());
		} else {
			secondLabel = new KLabelConstant(node.getRemainder().getName()+":"+node.getRemainder().getSort());
		}
		
		ArrayList<Term> resultList = new ArrayList<Term>();
		resultList.add(firstNode);
		resultList.add(kseqAdjust(secondLabel));
		return new KApp(new KLabelConstant("setLookUpPattern(_,_)"),new KList(resultList));
	}

	public Term kilToKore(MapImpl node) {
				
		java.util.List<Term> tempList = new java.util.ArrayList<Term>();

		for (java.util.Map.Entry<Term, Term> entry : node.map().entrySet()) {
			
			KSequence keyTerm = kseqAdjust(kilToKore(entry.getKey()));
			KSequence valueTerm = kseqAdjust(kilToKore(entry.getValue()));
			
			ArrayList<Term> newList = new ArrayList<Term>();
			newList.add(keyTerm);
			newList.add(valueTerm);
			tempList.add(kseqAdjust(new KApp(new KLabelConstant("_|->_"),new KList(newList))));
		}
		
		return new KList(tempList);
	}
	
	public Term kilToKore(SetImpl node) {
				
		java.util.List<Term> tempList = new java.util.ArrayList<Term>();
		tempList.addAll(node.getSet());
		
		for(int i=0;i<tempList.size();i++){
			
			KSequence elem = kseqAdjust((kilToKore(tempList.get(i))));
			tempList.set(i, elem);
		}
		
		return new KList(tempList);
	}
}
