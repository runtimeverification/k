package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.*;
import java.util.List;
import java.util.Map;
import java.util.Set;


/**
 * Transformer class compiling List accesses into lookup and update operations.
 *
 * @see org.kframework.kil.ListLookup
 * @see org.kframework.kil.ListUpdate
 *
 * @author TraianSF (refactoring from {@link SetToLookupUpdate})
 */
public class ListToLookupUpdate extends CopyOnWriteTransformer {

    private enum Status {LHS, RHS, CONDITION }

    private Map<Variable, ListUpdate> reverseMap = new HashMap<Variable, ListUpdate>();
    private ArrayList<ListLookup> queue = new ArrayList<ListLookup>();
    private Status status;

    public ListToLookupUpdate(Context context) {
        super("Compile lists into lookup and store operations", context);
    }

    @Override
    public ASTNode transform(Rule node) throws TransformerException {
        assert node.getBody() instanceof Rewrite:
               "expected rewrite at the top of rule " + node + ". "
               + "ListToLookupUpdate pass should be applied after ResolveRewrite pass.";

        reverseMap.clear();
        queue.clear();

        Rewrite rewrite = (Rewrite) node.getBody();
        status = Status.LHS;
        Term lhs = (Term) rewrite.getLeft().accept(this);

        List<BuiltinLookup> lookups = new ArrayList<BuiltinLookup>(node.getLookups());

        lookups.addAll(queue);
        queue.clear();

        status = Status.RHS;
        Term rhs = (Term) rewrite.getRight().accept(this);
        Term condition = node.getRequires();
        if (condition != null) {
            status = Status.CONDITION;
            condition = (Term) condition.accept(this);
        }

        //TODO: solve the ensures condition.

        if (lhs == rewrite.getLeft() && rhs == rewrite.getRight()
                && condition == node.getRequires()) {
            return node;
        }

        Rule returnNode = node.shallowCopy();
        rewrite = rewrite.shallowCopy();
        rewrite.setLeft(lhs, context);
        rewrite.setRight(rhs, context);
        returnNode.setBody(rewrite);
        returnNode.setRequires(condition);
        returnNode.setLookups(lookups);
        return returnNode;
    }

    @Override
    public ASTNode transform(ListBuiltin node) throws TransformerException {
        node = (ListBuiltin) super.transform(node);
        if (status == Status.LHS) {
            assert node.isLHSView();

            if (node.elementsLeft().isEmpty() && node.elementsRight().isEmpty()) {
                if (node.hasViewBase()) {
                    return node.viewBase();
                } else {
                    /* TODO(AndreiS): deal with empty data structures */
                }

            }

            Variable variable = Variable.getFreshVar(node.sort().name());
            if (node.hasViewBase()) {
                /* TODO(AndreiS): check the uniqueness of set variables in the LHS */
                reverseMap.put(
                        node.viewBase(),
                        new ListUpdate(variable, node.elementsLeft(), node.elementsRight()));
            }
            int key = 0;
            for (Term term : node.elementsLeft()) {
                queue.add(new ListLookup(variable,key, term));
                key++;
            }
            key = - node.elementsRight().size();
            for (Term term : node.elementsRight()) {
                queue.add(new ListLookup(variable, key, term));
                key++;
            }
            return variable;
        } else {
            /* status == Status.RHS || status == Status.CONDITION */
            List<Term> baseTerms = new ArrayList<Term>();
            java.util.List<Term> elementsLeft = new ArrayList<Term>(node.elementsLeft());
            java.util.List<Term> elementsRight = new ArrayList<Term>(node.elementsRight());
            for (Term term : node.baseTerms()) {
                if (!(term instanceof ListUpdate)) {
                    baseTerms.add(term);
                    continue;
                }
                ListUpdate listUpdate = (ListUpdate) term;

                List<Term> removeLeft = new ArrayList<Term>(listUpdate.removeLeft());
                List<Term> removeRight = new ArrayList<Term>(listUpdate.removeRight());

                ListIterator<Term> iteratorElem = elementsLeft.listIterator(elementsLeft.size());
                ListIterator<Term> iteratorRemove = removeLeft.listIterator(removeLeft.size());
                while (iteratorElem.hasPrevious() && iteratorRemove.hasPrevious() &&
                        iteratorElem.previous().equals(iteratorRemove.previous())) {
                    iteratorElem.remove();
                    iteratorRemove.remove();
                }
                iteratorElem = elementsRight.listIterator();
                iteratorRemove = removeRight.listIterator();
                while (iteratorElem.hasNext() && iteratorRemove.hasNext() &&
                        iteratorElem.next().equals(iteratorRemove.next())) {
                    iteratorElem.remove();
                    iteratorRemove.remove();
                }

                if (removeLeft.isEmpty() && removeRight.isEmpty()) {
                    baseTerms.add(listUpdate.base());
                } else {
                    baseTerms.add(new ListUpdate(listUpdate.base(), removeLeft, removeRight));
                }
            }

            assert baseTerms.size() <= 1 : "We don't support lists with more baseterms.";
            if (baseTerms.size() == 1 && elementsLeft.isEmpty() && elementsRight.isEmpty()) {
                /* if the ListBuiltin instance consists of only one base term,
                 * return the base term instead */
                return baseTerms.get(0);
            } else {
                return new ListBuiltin(node.sort(), elementsLeft, elementsRight, baseTerms);
            }
        }
    }

    @Override
    public ASTNode transform(Variable node) throws TransformerException {
        if (status != Status.LHS && reverseMap.containsKey(node)) {
            return reverseMap.get(node);
        } else {
            return node;
        }
    }

}
