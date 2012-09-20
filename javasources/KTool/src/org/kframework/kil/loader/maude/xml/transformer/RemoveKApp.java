package org.kframework.kil.loader.maude.xml.transformer;

import org.kframework.kil.loader.maude.xml.basic.Term;

public class RemoveKApp {
    
	/**
	 * 
	 * @param t the current node
	 * @return the next node to be processed
	 */
	public Term remove(Term t) {
		// for preprocessing
		Term toReturn = t;

		if (t.getOp().equals("_`(_`)") && t.getSort().equals("KItem")) {
			Term klabel = t.getChildren().get(0);
			if (klabel.getSort().equals("KLabel"))
				toReturn = klabel;
		}
        
		//propagare
		for (int i = 0; i < toReturn.getChildren().size(); i++) {
			Term newTerm = remove(toReturn.getChildren().get(i));
			toReturn.getChildren().set(i, newTerm);
		}
		return toReturn;
	}
}
