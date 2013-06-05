package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.BuiltinFunction;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;

import java.lang.reflect.InvocationTargetException;
import java.util.List;


/**
 *
 *
 * @author AndreiS
 */
public class KItem extends Term implements Sorted {

    private final KLabel kLabel;
    private final KList kList;
    private final String sort;

    public KItem(KLabel kLabel, KList kList, Context context) {
        super(Kind.KITEM);

        this.kLabel = kLabel;
        this.kList = kList;

        if (kLabel instanceof KLabelConstant) {
            List<Production> productions = ((KLabelConstant) kLabel).productions();
            if (productions.size() == 1) {
                Production production = productions.get(0);
                if (!kList.hasFrame() && kList.size() == production.getArity()) {
                    for (int i = 0; i < kList.size(); ++i) {
                        String childSort;
                        if (kList.get(i) instanceof Sorted) {
                            childSort = ((Sorted) kList.get(i)).sort();
                        } else {
                            childSort = kind.toString();
                        }

                        if (!context.isSubsortedEq(production.getChildSort(i), childSort)) {
                            sort = kind.toString();
                            return;
                        }
                    }
                    sort = production.getSort();
                } else {
                    sort = kind.toString();
                }
            } else {
                sort = kind.toString();
            }
        } else {
            if (kLabel instanceof KLabelInjection
                    && ((KLabelInjection) kLabel).term() instanceof BuiltinConstant) {
                sort = ((BuiltinConstant) ((KLabelInjection) kLabel).term()).getSort();
            } else {
                sort = kind.toString();
            }
        }
    }

    public KItem evaluateFunction() {
        if (!(kLabel instanceof KLabelConstant)) {
            return this;
        }

        for (Term term : kList.getItems()) {
            if (!term.isGround()) {
                return this;
            }
        }

        try {
            return BuiltinFunction.invoke(
                    (KLabelConstant) kLabel,
                    (Term[]) kList.getItems().toArray());
        } catch (IllegalArgumentException e) {
            e.printStackTrace();
        } catch (InvocationTargetException e) {
            e.printStackTrace();
        }

        return this;
    }

    public KLabel kLabel() {
        return kLabel;
    }

    public KList kList() {
        return kList;
    }

    @Override
    public boolean isSymbolic() {
        return kLabel.isFunction();
    }

    /**
     * @return a {@code String} representation of the sort of this K application.
     */
    @Override
    public String sort() {
        return sort;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KItem)) {
            return false;
        }

        KItem kItem = (KItem) object;
        return kLabel.equals(kItem.kLabel) && kList.equals(kItem.kList);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + kLabel.hashCode();
        hash = hash * Utils.HASH_PRIME + kList.hashCode();
        return hash;
    }

    @Override
    public String toString() {
        return kLabel + "(" + kList.toString() + ")";
    }

    @Override
    public void accept(Matcher matcher, Term patten) {
        matcher.match(this, patten);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

}
