// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import java.util.SortedSet;
import java.util.TreeSet;

import org.kframework.kil.Attributes;
import org.kframework.krun.api.SearchResult;
import org.kframework.krun.api.SearchResults;
import org.kframework.transformation.Transformation;
import org.kframework.utils.inject.InjectGeneric;

import com.google.inject.Inject;

public class PrintSearchResults implements Transformation<SearchResults, String> {

    @InjectGeneric private Transformation<SearchResult, String> searchResultPrinter;

    @Inject
    public PrintSearchResults() {}

    public PrintSearchResults(
            Transformation<SearchResult, String> searchResultPrinter) {
        this.searchResultPrinter = searchResultPrinter;
    }

    @Override
    public String run(SearchResults results, Attributes a) {
        StringBuilder sb = new StringBuilder();
        sb.append("Search results:");
        int i = 1;
        SortedSet<String> solutionStrings = new TreeSet<>();
        for (SearchResult solution : results.getSolutions()) {
            solutionStrings.add(searchResultPrinter.run(solution, a));
        }
        for (String solution : solutionStrings) {
            sb.append("\n\nSolution " + i + ":");
            sb.append(solution);
            i++;
        }
        if (i == 1) {
            sb.append("\nNo search results");
        }
        return sb.toString();
    }

    @Override
    public String getName() {
        return "Print search results";
    }

}
