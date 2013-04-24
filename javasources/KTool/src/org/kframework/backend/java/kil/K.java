package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Sorted;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Production;
import org.kframework.kil.loader.DefinitionHelper;

import java.util.List;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/18/13
 * Time: 12:18 PM
 * To change this template use File | Settings | File Templates.
 */
public class K extends Term implements Sorted {

    private final KLabel kLabel;
    private final KList kList;
    private final String sort;

    public K(KLabel kLabel, KList kList) {
        super("K");

        this.kLabel = kLabel;
        this.kList = kList;

        if (kLabel instanceof KLabelConstant) {
            List<Production> productions = Utils.productionsOf(((KLabelConstant) kLabel).getLabel());
            if (productions.size() == 1) {
                Production production = productions.get(0);
                if (!kList.hasFrame() && kList.size() == production.getArity()) {
                    for (int i = 0; i < kList.size(); ++i) {
                        String sort;
                        if (kList.get(i) instanceof Sorted) {
                            sort = ((Sorted) kList.get(i)).getSort();
                        } else {
                            sort = "K";
                        }

                        if (DefinitionHelper.isSubsortedEq(production.getChildSort(i), sort)) {
                            sort = "K";
                            break;
                        }
                    }
                    sort = production.getSort();
                } else {
                    sort = "K";
                }
            } else {
                sort = "K";
            }
        } else {
            if (kLabel instanceof KLabelInjection && ((KLabelInjection) kLabel).getTerm() instanceof BuiltinConstant) {
                sort = ((BuiltinConstant) ((KLabelInjection) kLabel).getTerm()).getSort();
            } else {
                sort = "K";
            }
        }
    }

    public KLabel getKLabel() {
        return kLabel;
    }

    public KList getKList() {
        return kList;
    }

    /**
     * @return the string representation of the sort of this K application.
     */
    @Override
    public String getSort() {
        return sort;
    }

    @Override
    public boolean isSymbolic() {
        return kLabel.isFunction();
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof K)) {
            return false;
        }

        K k = (K) object;
        return kLabel.equals(k.kLabel) && kList.equals(k.kList) && sort.equals(k.sort);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + kLabel.hashCode();
        hash = hash * Utils.HASH_PRIME + kList.hashCode();
        hash = hash * Utils.HASH_PRIME + sort.hashCode();
        return hash;
    }

    @Override
    public String toString() {
        String kListString = kList.toString();
        return !kListString.isEmpty() ? kLabel + "(" + kListString + ")" : kLabel.toString();
    }

    /**
     * @return a copy of the ASTNode containing the same fields.
     */
    @Override
    public ASTNode shallowCopy() {
        return new K(this.kLabel, this.kList);
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
