// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.definition.Rule;
import org.kframework.kore.K;

/**
 * Created by manasvi on 9/4/15.
 * Object Containing the results of a search operation.
 */
public class SearchResult {
    private K searchList;
    private Rule parsedRule;

    public SearchResult(K searchList, Rule parsedRule) {
        this.searchList = searchList;
        this.parsedRule = parsedRule;
    }

    public K getSearchList() {
        return searchList;

    }

    public Rule getParsedRule() {
        return parsedRule;
    }

}
