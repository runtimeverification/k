package main;

import transformer.JavaClassesFactory;
import basic.Term;

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
