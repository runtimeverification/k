package org.kframework.backend.java.kil;

import com.google.common.collect.ImmutableSet;
import org.kframework.kil.ASTNode;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Set;


/**
 * A K definition in the format of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public class Definition extends ASTNode {

    public static final Set<String> TOKEN_SORTS = ImmutableSet.of("Bool", "Int", "Id");

    private final Set<Rule> rules;
    private final Set<KLabelConstant> kLabels;
    private final Set<KLabelConstant> frozenKLabels;

    public Definition(
            Set<Rule> rules,
            Set<KLabelConstant> kLabels,
            Set<KLabelConstant> frozenKLabels) {
        this.rules = rules;
        this.kLabels = kLabels;
        this.frozenKLabels = frozenKLabels;
    }

    public Set<Rule> rules() {
        return rules;
    }

    public Set<KLabelConstant> kLabels() {
        return kLabels;
    }

    public Set<KLabelConstant> frozenKLabels() {
        return frozenKLabels;
    }

    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        throw new UnsupportedOperationException();
    }

    @Override
    public void accept(Visitor visitor) {
        throw new UnsupportedOperationException();
    }

}
