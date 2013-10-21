package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Filter the rule side condition such that it contains only
 * SMTLIB translatable items. The filtered terms are stored
 * in a list for further use.
 *
 * @author andreiarusoaie
 */
public class ConditionTransformer extends CopyOnWriteTransformer {

    List<Term> filteredTerms = new ArrayList<Term>();

    public ConditionTransformer(Context context) {
        super("Filter side conditions", context);
    }

    @Override
    public ASTNode transform(KApp node) throws TransformerException {
        Term label = node.getLabel();
        if (label instanceof KLabelConstant) {
            Term content = node.getChild();
            if (label.equals(KLabelConstant.ANDBOOL_KLABEL)) {
                if (content instanceof KList) {
                    List<Term> terms = ((KList) content).getContents();
                    List<Term> remainingTerms = new ArrayList<Term>();
                    for (Term t : terms) {
                        CheckSmtlibVisitor csv = new CheckSmtlibVisitor(context);
                        t.accept(csv);
                        if (csv.smtValid())
                            filteredTerms.add(t.shallowCopy());
                        else remainingTerms.add(t.shallowCopy());
                    }
                    content = new KList(remainingTerms);
                }
            } else {
                CheckSmtlibVisitor csv = new CheckSmtlibVisitor(context);
                content.accept(csv);
                if (csv.smtValid()) {
                    filteredTerms.add(content.shallowCopy());
                    content = new KList();
                }
            }

            node = node.shallowCopy();
            node.setChild(content);
            return node;
        }

        return super.transform(node);
    }

    public List<Term> getFilteredTerms() {
        return filteredTerms;
    }
}
