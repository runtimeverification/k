package main;

import basic.Term;

public class Main {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		Term t = Term.loadTermFromFile("sum.imp.xml");
		
		System.out.println(t);
		
		
	}

}
