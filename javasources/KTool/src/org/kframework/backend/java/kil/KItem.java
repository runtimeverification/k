package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.Sorted;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;

import java.util.List;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/18/13
 * Time: 12:18 PM
 * To change this template use File | Settings | File Templates.
 */
public class KItem extends Term implements Sorted {

    private final KLabel kLabel;
    private final KList kList;
    private final String sort;
    private Context context;

    public KItem(KLabel kLabel, KList kList, Context context) {
        super(Kind.KITEM);
    	this.context = context;

        this.kLabel = kLabel;
        this.kList = kList;

        if (kLabel instanceof KLabelConstant) {
            List<Production> productions = ((KLabelConstant) kLabel).productionsOf(context);
            if (productions.size() == 1) {
                Production production = productions.get(0);
                if (!kList.hasFrame() && kList.size() == production.getArity()) {
                    for (int i = 0; i < kList.size(); ++i) {
                        String childSort;
                        if (kList.get(i) instanceof Sorted) {
                            childSort = ((Sorted) kList.get(i)).getSort();
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
                    sort = kind.toString();;
                }
            } else {
                sort = kind.toString();
            }
        } else {
            if (kLabel instanceof KLabelInjection && ((KLabelInjection) kLabel).getTerm() instanceof BuiltinConstant) {
                sort = ((BuiltinConstant) ((KLabelInjection) kLabel).getTerm()).getSort();
            } else {
                sort = kind.toString();
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
        String kListString = kList.toString();
        return !kListString.isEmpty() ? kLabel + "(" + kListString + ")" : kLabel.toString();
    }

    /**
     * @return a copy of the ASTNode containing the same fields.
     */
    @Override
    public ASTNode shallowCopy() {
        return new KItem(this.kLabel, this.kList, this.context);
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
