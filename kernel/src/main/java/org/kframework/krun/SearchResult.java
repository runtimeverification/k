package org.kframework.krun;

import org.kframework.kore.K;
import org.kframework.kore.KVariable;

import java.util.Collections;
import java.util.List;
import java.util.Map;

/**
 * Created by manasvi on 9/4/15.
 * Object Containing the results of a search operation.
 *
 */
public class SearchResult {
    private final List<? extends Map<? extends KVariable, ? extends K>> searchList;

    public SearchResult(List<? extends Map<? extends KVariable, ? extends K>> searchList) {
        this.searchList = searchList;
    }

    public List<? extends Map<? extends KVariable, ? extends K>> getSearchList() {
        return Collections.unmodifiableList(searchList);
    }
}
