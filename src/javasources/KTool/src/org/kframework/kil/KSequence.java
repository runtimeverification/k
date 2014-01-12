package org.kframework.kil;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import aterm.ATermAppl;

/** Represents the contents (all of sort KItem) joined by ~>. */
public class KSequence extends Collection {

	public static final KSequence EMPTY = new KSequence(Collections.<Term> emptyList());

	public KSequence(Element element) {
		super(element);
	}

	public KSequence(KSequence node) {
		super(node);
	}

	public KSequence(ATermAppl atm) {
		super(atm);
	}

	public KSequence() {
		super("K");
	}

	public KSequence(List<Term> col) {
		super("K", col);
	}

	@Override
	public String toString() {
		String content = "";
		for (int i = 0; i < contents.size(); i++) {
			if (i == contents.size() - 1)
				content += contents.get(i);
			else
				content += contents.get(i) + "~> ";
		}
        if (content.equals("")) return ".K";
		return content;
	}

	@Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

	@Override
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

	@Override
	public void accept(Matcher matcher, Term toMatch) {
		matcher.match(this, toMatch);
	}

	@Override
	public KSequence shallowCopy() {
		return new KSequence(this);
	}
	
	public static KSequence wrap(KApp item){
		
		List<Term> tempList = new ArrayList<Term>();
		tempList.add(item);
		
		return new KSequence(tempList);
	}
	
	/*
	 * Liyi Li
	 * input either KList KItem K or KLabel and return the wraping KSequence
	 * 
	 */
	public static KSequence adjust(Term item){
		
		if(item instanceof KList){
			KApp temp = new KApp(new KLabelConstant("List"),item);
			return KSequence.wrap(temp);
		} else if (item instanceof KSequence) {
			return (KSequence) item;
		} else if (item instanceof KApp) {
			return KSequence.wrap((KApp) item);
		} else if (item instanceof KLabel) {
			return KSequence.wrap(KApp.wrap((KLabel) item));
		} else if ((item instanceof Bag) || (item instanceof Cell)) {
			List<Term> tempList = new ArrayList<Term>();
			tempList.add(item);
			return new KSequence(tempList);
		} else {
			return null;
		}
	}

	@Override
	public Term kilToKore() {
		
		List<Term> resultList = new ArrayList<Term>();
		
		for(int i=0;i<this.contents.size();++i){
			
			KSequence temp = KSequence.adjust(this.contents.get(i).kilToKore());
			resultList.addAll(temp.getContents());
		}
		
		return new KSequence(resultList);
	}
}
