// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import java.util.Map;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.Term;
import org.kframework.transformation.Transformation;
import org.kframework.utils.inject.InjectGeneric;

import com.google.inject.Inject;

public class PrintSearchResult implements Transformation<Map<String, Term>, String> {

    @InjectGeneric private Transformation<ASTNode, String> prettyPrinter;

    @Inject
    public PrintSearchResult() {}

    public PrintSearchResult(
            Transformation<ASTNode, String> prettyPrinter) {
        this.prettyPrinter = prettyPrinter;
    }

    public static final String IS_DEFAULT_PATTERN = "isDefaultPattern";

    @Override
    public String run(Map<String, Term> substitution, Attributes a) {
        StringBuilder sb = new StringBuilder();
        if (a.typeSafeGet(Boolean.class, IS_DEFAULT_PATTERN)) {
            sb.append("\n");
            sb.append(prettyPrinter.run(substitution.get("B:Bag"), a));
        } else {
            boolean empty = true;

            for (String variable : substitution.keySet()) {
                sb.append("\n");
                sb.append(variable);
                sb.append(" -->\n");
                sb.append(prettyPrinter.run(substitution.get(variable), a));
                empty = false;
            }
            if (empty) {
                sb.append("\nEmpty substitution");
            }
        }
        return sb.toString();
    }

    @Override
    public String getName() {
        return "print substitution";
    }
}
