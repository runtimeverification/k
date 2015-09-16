// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.definition.Rule;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Created by manasvi on 9/4/15.
 * Object Containing the results of a search operation.
 */
public class SearchResult {
    private List<? extends Map<? extends KVariable, ? extends K>> searchList;
    private Rule parsedRule;

    public SearchResult(List<? extends Map<? extends KVariable, ? extends K>> searchList, Rule parsedRule) {
        this.searchList = searchList;
        this.parsedRule = parsedRule;
    }

    public List<? extends Map<? extends KVariable, ? extends K>> getSearchList() {
        return searchList == null ? null : Collections.unmodifiableList(searchList);

    }

    public Rule getParsedRule() {
        return parsedRule;
    }

}
