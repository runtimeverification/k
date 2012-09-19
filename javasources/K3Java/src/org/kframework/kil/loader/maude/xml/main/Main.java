package org.kframework.kil.loader.maude.xml.main;

import org.kframework.kil.loader.maude.xml.basic.Term;
import org.kframework.kil.loader.maude.xml.transformer.JavaClassesFactory;


public class Main {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		Term t = Term.loadTermFromFile("sum.imp.xml");
		
		System.out.println(t);
		
		org.kframework.kil.Term t2 = JavaClassesFactory.getTerm(t);
		System.out.println(t2);
	}

}
