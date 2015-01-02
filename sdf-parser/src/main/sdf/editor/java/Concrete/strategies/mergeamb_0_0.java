// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package Concrete.strategies;

import java.util.ArrayList;

import org.spoofax.interpreter.terms.IStrategoAppl;
import org.spoofax.interpreter.terms.IStrategoConstructor;
import org.spoofax.interpreter.terms.IStrategoInt;
import org.spoofax.interpreter.terms.IStrategoList;
import org.spoofax.interpreter.terms.IStrategoString;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

/**
 * Example Java strategy implementation.
 *
 * This strategy can be used by editor services and can be called in Stratego modules by declaring it as an external strategy as follows:
 *
 * <code>
 *  external mergeamb(|)
 * </code>
 *
 * @see InteropRegisterer This class registers string_trim_last_one_0_0 for use.
 */
public class mergeamb_0_0 extends Strategy {

    public static mergeamb_0_0 instance = new mergeamb_0_0();


    /**
     * Restructure a node
     * from: [A(x1, x2 ... xn), A(y1, y2 ... yn), A ..., B]
     * to  : [A(amb([x1, y1, ...]), amb([x2, y2, ...]), ... amb([xn, yn, ...])), B]
     *
     * if the children of every A are located in the same places (see isSimilar(...)).
     */
    @Override
    public IStrategoTerm invoke(Context context, IStrategoTerm currentList) {
        context.push("mergeamb_0_0");

        java.util.List<IStrategoTerm> children = new ArrayList<IStrategoTerm>();
        //IStrategoTerm currentList = amb.getSubterm(0);
        for (int i = 0; i < currentList.getSubtermCount(); i++)
            children.add((IStrategoTerm) currentList.getSubterm(i));

        java.util.List<IStrategoTerm> newchildren = new ArrayList<IStrategoTerm>();

        // while there are still children that haven't been processed
        while (!children.isEmpty()) {
            // group the similar children
            IStrategoTerm head = children.get(0);
            java.util.List<IStrategoTerm> similar = new ArrayList<IStrategoTerm>();
            similar.add(head);
            for (int i = 1; i < children.size(); i++) {
                if (isSimilar(head, children.get(i), context)) {
                    similar.add(children.get(i));
                }
            }

            // remove the grouped nodes from the children list
            children.removeAll(similar);

            //context.getIOAgent().printError(similar.size() + "=" + head);

            // create a new node that combines the children in new ambiguity nodes
            if (similar.size() > 1) {
                java.util.List<IStrategoTerm> termList = new ArrayList<IStrategoTerm>();

                for (int i = 0; i < head.getSubtermCount(); i++) {
                    IStrategoConstructor ambc = context.getFactory().makeConstructor("amb", 1);

                    java.util.List<IStrategoTerm> list2 = new ArrayList<IStrategoTerm>();
                    for (int j = 0; j < similar.size(); j++)
                        list2.add(similar.get(j).getSubterm(i));

                    IStrategoList ambl = context.getFactory().makeList(list2);
                    IStrategoAppl ambappl = context.getFactory().makeAppl(ambc, ambl);
                    ambappl = (IStrategoAppl)context.getFactory().annotateTerm(ambappl, head.getSubterm(i).getAnnotations());

                    termList.add(ambappl);
                }
                IStrategoConstructor newtermConstr = ((IStrategoAppl)head).getConstructor();
                IStrategoList newtermList = context.getFactory().makeList(termList);
                IStrategoAppl newtermAppl = context.getFactory().makeAppl(newtermConstr, newtermList.getAllSubterms(), null);
                newtermAppl = (IStrategoAppl)context.getFactory().annotateTerm(newtermAppl, head.getAnnotations());
                newchildren.add(newtermAppl);
            }
            else {
                // if there is only one child, just add it to the new list
                newchildren.add(similar.get(0));
            }
        }

        IStrategoList ambl = context.getFactory().makeList(newchildren);

        context.popOnSuccess();
        return ambl;
    }

    /**
     * Check if two terms are similar. Meaning they have the same constructor, and the children are located in the same places.
     * @param t1 - first term.
     * @param t2 - second term.
     * @param context - the context in which to compare them.
     * @return - true if the terms are similar, false otherwise.
     */
    private boolean isSimilar(IStrategoTerm t1, IStrategoTerm t2, Context context) {
        if (t1.getTermType() != t2.getTermType())
            return false;

        if (t1.getTermType() == IStrategoTerm.APPL)
            if (!((IStrategoAppl) t1).getName().equals(((IStrategoAppl) t2).getName()))
                return false;
        if (t1.getTermType() == IStrategoTerm.STRING)
            if (!((IStrategoString) t1).stringValue().equals(((IStrategoString) t2).stringValue()))
                return false;
        if (t1.getTermType() == IStrategoTerm.INT)
            if (((IStrategoInt) t1).intValue() != ((IStrategoInt) t2).intValue())
                return false;

        for (int i = 0; i < t1.getSubtermCount(); i++) {
            IStrategoTerm ch1 = t1.getSubterm(i);
            IStrategoTerm ch2 = t2.getSubterm(i);
            IStrategoTerm loc1 = ch1.getAnnotations();
            IStrategoTerm loc2 = ch2.getAnnotations();

            if (loc1 == null)
                context.getIOAgent().printError("Error1: " + ch1);
            if (loc2 == null)
                context.getIOAgent().printError("Error2: " + ch2);

            if (!loc1.toString().equals(loc2.toString()))
                return false;
        }
        return true;
    }

}
