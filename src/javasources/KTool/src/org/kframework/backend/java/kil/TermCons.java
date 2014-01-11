package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;

import com.google.common.collect.ImmutableList;

public class TermCons extends Term {
    
    private final String cons;
    private final java.util.List<Term> contents;
    private final org.kframework.kil.Production production;

    public TermCons(String cons, java.util.List<Term> contents, Context context) {
        super(Kind.of(context.conses.get(cons).getSort()));
        this.cons = cons;
        this.contents = ImmutableList.<Term>copyOf(contents);
        this.production = context.conses.get(cons);
    }
    
    public String cons() {
        return cons;
    }
    
    public java.util.List<Term> contents() {
        return contents;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public boolean isSymbolic() {
        return false;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof TermCons)) {
            return false;
        }

        TermCons termCons = (TermCons) object;
        return cons.equals(termCons.cons) && contents.equals(termCons.contents);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + cons.hashCode();
        hash = hash * Utils.HASH_PRIME + contents.hashCode();
        return hash;
    }
    
    @Override
    public String toString() {
        String str = "";
        if (production.getItems().size() > 0) {
            if (production.getItems().get(0) instanceof org.kframework.kil.UserList) {
                String separator = ((org.kframework.kil.UserList) production
                        .getItems().get(0)).getSeparator();
                str = contents.get(0) + " " + separator + " " + contents.get(1)
                        + " ";
            } else
                for (int i = 0, j = 0; i < production.getItems().size(); i++) {
                    org.kframework.kil.ProductionItem pi = production
                            .getItems().get(i);
                    if (pi instanceof org.kframework.kil.Terminal) {
                        String terminall = pi.toString();
                        terminall = terminall.substring(1,
                                terminall.length() - 1);
                        str += terminall + " ";
                    } else if (pi instanceof org.kframework.kil.Sort)
                        str += contents.get(j++) + " ";
                }
        }
        return str;
    }
}
