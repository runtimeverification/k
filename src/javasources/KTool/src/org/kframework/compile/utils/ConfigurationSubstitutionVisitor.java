package org.kframework.compile.utils;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.HashMap;
import java.util.Map;

/**
 * Created with IntelliJ IDEA.
 * User: Traian
 * Date: 11/7/13
 * Time: 1:51 PM
 * To change this template use File | Settings | File Templates.
 */
public class ConfigurationSubstitutionVisitor extends BasicVisitor {

    private final Map<Term, Term> substitution;
    public ConfigurationSubstitutionVisitor(Context context) {
        super(context);
        substitution = new HashMap<>();
    }

    public Map<Term, Term> getSubstitution() {
        return substitution;
    }

    @Override
    public void visit(Cell cell) {
        if (cell.getContents() instanceof Bag) {
            super.visit(cell);
        } else {
            substitution.put(new Variable(cell.getLabel().toUpperCase(), cell.getContents().getSort()),
                    cell.getContents());
        }
    }
}
