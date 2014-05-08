// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck.utils;

import org.kframework.kil.Rewrite;
import org.kframework.kil.Sentence;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class ReachabilityRuleKILParser extends BasicVisitor {

    private Term pi;
    private Term phi;
    private Term pi_prime;
    private Term phi_prime;

    public ReachabilityRuleKILParser(Context context) {
        super(context);
    }

    public Void visit(Sentence node, Void _) {
        
        if (node.getBody() instanceof Rewrite) {
            Rewrite rew = (Rewrite) node.getBody();
            pi = rew.getLeft();
            pi_prime = rew.getRight();
        }
        
        phi = node.getRequires();
        phi_prime = node.getEnsures();
        return null;
    }

    public Term getPi() {
        return pi;
    }

    public Term getPhi() {
        return phi;
    }

    public Term getPi_prime() {
        return pi_prime;
    }

    public Term getPhi_prime() {
        return phi_prime;
    }
}
