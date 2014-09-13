// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck;

import java.util.LinkedList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Rule;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class RetrieveRRVisitor extends BasicVisitor {

    List<ASTNode> rules = new LinkedList<ASTNode>();

    public RetrieveRRVisitor(Context context) {
        super(context);
    }

    @Override
    public Void visit(Rule node, Void _) {
        rules.add(node);
        return super.visit(node, _);
    }

    public List<ASTNode> getRules() {
        return rules;
    }
}
