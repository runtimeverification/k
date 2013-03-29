package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Constant;
import org.kframework.kil.KApp;
import org.kframework.kil.KList;
import org.kframework.kil.Term;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Collapse nested conjunctions like _andBool_(_andBool_(t1, t2), t3)
 * into andBool(t1,t2,t3).
 *
 * @author andreiarusoaie
 */
public class CollapseAndBoolTransformer extends CopyOnWriteTransformer {

    public CollapseAndBoolTransformer() {
        super("Collapse nested conjunctions.");
    }

    @Override
    public ASTNode transform(KApp node) throws TransformerException {

        Term label = node.getLabel();
        Term newContent = node.getChild().shallowCopy();
        if (label instanceof Constant) {
            String labelName = ((Constant) label).getValue();

            if (labelName
                    .equals(Constant.BOOL_ANDBOOL_KLABEL.getValue().trim())) {
                node = node.shallowCopy();
                node.setLabel(Constant.ANDBOOL_KLABEL);
                return transform(node);
            }

            if (labelName.equals(Constant.ANDBOOL_KLABEL.getValue().trim())) {
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
                                if (tlabel instanceof Constant) {
                                    Constant ct = (Constant) tlabel;
                                    if (ct.getValue().equals(
                                            Constant.ANDBOOL_KLABEL.getValue()
                                                    .trim())
                                            || ct.getValue()
                                            .equals(Constant.BOOL_ANDBOOL_KLABEL
                                                    .getValue().trim())) {
                                        newList.add(tapp.getChild()
                                                .shallowCopy());
                                        collapsed = true;
                                    }
                                }
                            }
                            if (!collapsed)
                                newList.add(t);
                        }
                        newContent = new KList(newList);
                    }
                } else if (content instanceof KApp) {
                    Term aLabel = ((KApp) content).getLabel();
                    if (aLabel instanceof Constant) {
                        if (((Constant) aLabel).getValue().equals(
                                Constant.ANDBOOL_KLABEL.getValue().trim())
                                || ((Constant) aLabel).getValue().equals(
                                Constant.BOOL_ANDBOOL_KLABEL.getValue()
                                        .trim()))
                            newContent = ((KApp) content).getChild().shallowCopy();
                    }
                }
            }
            node = node.shallowCopy();
            node.setChild(newContent);
            return node;
        }

        return super.transform(node);
    }
}
