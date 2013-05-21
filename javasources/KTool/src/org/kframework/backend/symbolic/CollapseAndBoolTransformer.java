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
 * Collapse nested conjunctions like _andBool_(_andBool_(t1, t2), t3)
 * into andBool(t1,t2,t3).
 *
 * @author andreiarusoaie
 */
public class CollapseAndBoolTransformer extends CopyOnWriteTransformer {

    public CollapseAndBoolTransformer(Context context) {
        super("Collapse nested conjunctions.", context);
    }

    @Override
    public ASTNode transform(KApp node) throws TransformerException {
        Term label = node.getLabel();
        Term newContent = node.getChild().shallowCopy();
        if (label instanceof KLabelConstant) {
            KLabelConstant kLabelConstant = (KLabelConstant) label;

            if (kLabelConstant.equals(KLabelConstant.BOOL_ANDBOOL_KLABEL)) {
                node = node.shallowCopy();
                node.setLabel(KLabelConstant.ANDBOOL_KLABEL);
                return transform(node);
            }

            if (kLabelConstant.equals(KLabelConstant.ANDBOOL_KLABEL)) {
                Term content = node.getChild();
                if (content instanceof KList) {
                    List<Term> list = ((KList) content).getContents();
                    List<Term> newList = new ArrayList<Term>();

                    boolean collapsed;
                    if (list != null) {
                        for (Term t : list) {
                            collapsed = false;
                            if (t instanceof KApp) {
                                KApp tapp = (KApp) t;
                                Term tlabel = tapp.getLabel();
                                if (tlabel.equals(KLabelConstant.BOOL_ANDBOOL_KLABEL)
                                        || tlabel.equals(KLabelConstant.ANDBOOL_KLABEL)) {
                                    newList.add(tapp.getChild().shallowCopy());
                                    collapsed = true;
                                }
                            }
                            if (!collapsed)
                                newList.add(t);
                        }
                        newContent = new KList(newList);
                    }
                } else if (content instanceof KApp) {
                    Term aLabel = ((KApp) content).getLabel();
                    if (aLabel.equals(KLabelConstant.BOOL_ANDBOOL_KLABEL)
                            || aLabel.equals(KLabelConstant.ANDBOOL_KLABEL))
                        newContent = ((KApp) content).getChild().shallowCopy();
                }
            }
            node = node.shallowCopy();
            node.setChild(newContent);
            return node;
        }

        return super.transform(node);
    }
}
