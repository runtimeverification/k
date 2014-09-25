// Copyright (c) 2012-2014 K Team. All Rights Reserved.

package org.kframework.backend.symbolic;

import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

/**
 * This class extracts the LTL state from K rules defining the LTL satisfaction relation.
 * The following rule satisfies the satisfaction relation for the predicate "eqTo":
 *
 *   rule B:Bag |=Ltl eqTo(X:Id, I:Int) => true requires val(B, X) ==Int I [ltl, anywhere]
 *
 * The LTL state computed by this visitor class is the variable B:Bag.
 */
public class SearchLTLState extends BasicVisitor {

    // the LTL state term
    private Term ltlState;

    public SearchLTLState(Context context) {
        super("Search LTL state rules defining LTL satisfaction relation", context);
        ltlState = null;
    }

    @Override
    public Void visit(Rule node, Void _) {
        Term body = node.getBody();
        if (body instanceof Rewrite) {
            // isolate the left hand side of the rule and search for '_|=Ltl_
            Rewrite rewrite = (Rewrite) body;
            Term rewriteLHS = rewrite.getLeft();
            if (rewriteLHS instanceof KApp) {
                // extract the left hand side top KApp
                KApp rewriteLHSBody = (KApp) rewriteLHS;
                if (rewriteLHSBody.getLabel() instanceof KLabelConstant) {
                    // get left hand side KLabel
                    KLabelConstant rewriteLHSLabel = (KLabelConstant) rewriteLHSBody.getLabel();

                    // check if the left hand side KLabel is '|=Ltl
                    if (rewriteLHSLabel.getLabel().equals(ResolveLtlAttributes.LTL_SAT)) {
                        // Extract the components of the '|=Ltl KApp body
                        KList rewriteLHSContents = (KList) rewriteLHSBody.getChild();
                        ltlState = rewriteLHSContents.getContents().get(0);
                        return null;
                    }
                }
            }
        }
        return null;
    }

    public Term getLtlState() {
        return ltlState;
    }
}