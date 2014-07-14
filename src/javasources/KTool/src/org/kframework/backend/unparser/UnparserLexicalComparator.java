// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;

import org.kframework.kil.Term;

import com.davekoelle.AlphanumComparator;

public class UnparserLexicalComparator implements Comparator<Term> {
    
    AlphanumComparator comparator = new AlphanumComparator();
    Map<Term, String> unparsed = new HashMap<>();
    
    public UnparserLexicalComparator(Map<Term, String> unparsed) {
        this.unparsed = unparsed;
    }
    
    @Override
    public int compare(Term o1, Term o2) {
        return comparator.compare(unparsed.get(o1), unparsed.get(o2));
    }
}
