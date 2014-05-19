// Copyright (c) 2013-2014 K Team. All Rights Reserved.
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
    public ASTNode visit(KApp node, Void _)  {
        return recursiveCollapseAndBool(node);
    }
    
    private KApp recursiveCollapseAndBool(KApp node) {
        Term label = node.getLabel();
        if (label instanceof KLabelConstant) {
            KLabelConstant kLabelConstant = (KLabelConstant) label;

            if (kLabelConstant.equals(KLabelConstant.BOOL_ANDBOOL_KLABEL)) {
                node = node.shallowCopy();
                node.setLabel(KLabelConstant.ANDBOOL_KLABEL);
                return recursiveCollapseAndBool(node);
            }

            Term newContent = node.getChild();
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
                                KApp tapp = recursiveCollapseAndBool((KApp) t);
                                Term tlabel = tapp.getLabel();
                                if (tlabel.equals(KLabelConstant.BOOL_ANDBOOL_KLABEL)
                                        || tlabel.equals(KLabelConstant.ANDBOOL_KLABEL)) {
                                    Term term = tapp.getChild().shallowCopy();
                                    if (term instanceof KList) {
                                        KList listTerm = (KList) term;
                                        List<Term> listContent = listTerm.getContents();
                                        for(Term lt : listContent) {
                                            newList.add(lt);
                                        }
                                    }
                                    else {
                                        newList.add(tapp.getChild().shallowCopy());
                                    }
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
                            || aLabel.equals(KLabelConstant.ANDBOOL_KLABEL)){
                        
                        Term resolved = recursiveCollapseAndBool((KApp)content);
                        
                        List<Term> newList = new ArrayList<Term>();
                        newList.add(resolved.shallowCopy());
                        newContent = new KList(newList);
                    }
                }
            }
            return new KApp(node.getLabel(), newContent);
        }

        return node;
    }
}
