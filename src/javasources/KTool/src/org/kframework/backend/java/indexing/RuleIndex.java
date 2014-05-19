// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;

import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;

import java.util.List;

/**
 * Author: OwolabiL
 * Date: 3/7/14
 * Time: 1:26 PM
 */
public interface RuleIndex {
    void buildIndex();
    List<Rule> getRules(Term term);
}
