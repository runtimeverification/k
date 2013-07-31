package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.Collection;
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
 * Transformer class compiling Set accesses into lookup and update operations.
 *
 * @see org.kframework.kil.SetLookup
 * @see org.kframework.kil.SetUpdate
 *
 * @author AndreiS
 */
public class SetToLookupUpdate extends CopyOnWriteTransformer {

    private class ExtendedSetLookup extends SetLookup {
        public Set<Variable> variables;

        ExtendedSetLookup(Term value, Variable set) {
            super(set, value);
            variables = value.variables();
        }
    }

    private enum Status {LHS, RHS, CONDITION }

    private Map<Variable, SetUpdate> reverseMap = new HashMap<Variable, SetUpdate>();
    private ArrayList<ExtendedSetLookup> queue = new ArrayList<ExtendedSetLookup>();
    private Status status;

    public SetToLookupUpdate(Context context) {
        super("Compile sets into lookup and store operations", context);
    }

    @Override
    public ASTNode transform(Rule node) throws TransformerException {
        assert node.getBody() instanceof Rewrite:
               "expected rewrite at the top of rule " + node + ". "
               + "SetToLookupUpdate pass should be applied after ResolveRewrite pass.";

        reverseMap.clear();
        queue.clear();

        Rewrite rewrite = (Rewrite) node.getBody();
        status = Status.LHS;
        Term lhs = (Term) rewrite.getLeft().accept(this);

        List<BuiltinLookup> lookups = new ArrayList<BuiltinLookup>(node.getLookups());

        for (ExtendedSetLookup item : queue) {
            item.variables.removeAll(lhs.variables());
        }

        boolean change;
        do {
            change = false;
            for (int i = 0; i < queue.size(); ++i) {
                if (queue.get(i).variables.isEmpty()) {
                    change = true;
                    SetLookup lookup = queue.remove(i);
                    lookups.add(new SetLookup(lookup.base(), lookup.key()));

                    for (ExtendedSetLookup extendedLookup : queue) {
                        extendedLookup.variables.removeAll(lookup.key().variables());
                    }
                }
            }
        } while (change);

        if (!queue.isEmpty()) {
            /* TODO(AndreiS): handle iteration over sets */
            GlobalSettings.kem.register(new KException(
                    KException.ExceptionType.WARNING,
                    KException.KExceptionGroup.CRITICAL,
                    "Unsupported set pattern in the rule left-hand side",
                    node.getFilename(),
                    node.getLocation()));
            return node;
        }

        status = Status.RHS;
        Term rhs = (Term) rewrite.getRight().accept(this);
        Term requires = node.getRequires();
        if (requires != null) {
            status = Status.CONDITION;
            requires = (Term) requires.accept(this);
        }

        Term ensures = node.getEnsures();
        //TODO: update to include ensures.
        if (lhs == rewrite.getLeft() && rhs == rewrite.getRight()
                && requires == node.getRequires() && ensures == node.getEnsures()) {
            return node;
        }

        Rule returnNode = node.shallowCopy();
        rewrite = rewrite.shallowCopy();
        rewrite.setLeft(lhs, context);
        rewrite.setRight(rhs, context);
        returnNode.setBody(rewrite);
        returnNode.setRequires(requires);
        returnNode.setEnsures(ensures);
        returnNode.setLookups(lookups);
        return returnNode;
    }

    @Override
    public ASTNode transform(SetBuiltin node) throws TransformerException {
        node = (SetBuiltin) super.transform(node);
        if (status == Status.LHS) {
            assert node.isLHSView();

            if (node.elements().isEmpty()) {
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
                        new SetUpdate(variable, node.elements(), Collections.<Term>emptySet()));
            }
            for (Term term : node.elements()) {
                queue.add(new ExtendedSetLookup(term, variable));
            }
            return variable;
        } else {
            /* status == Status.RHS || status == Status.CONDITION */
            List<Term> baseTerms = new ArrayList<Term>();
            java.util.Collection<Term> elements = new ArrayList<Term>(node.elements());
            for (Term term : node.baseTerms()) {
                if (!(term instanceof SetUpdate)) {
                    baseTerms.add(term);
                    continue;
                }
                SetUpdate setUpdate = (SetUpdate) term;

                java.util.Collection<Term> removeEntries = new ArrayList<Term>();
                java.util.Collection<Term> updateEntries = new ArrayList<Term>();
                for (Term key : setUpdate.removeEntries()) {
                    if (elements.contains(key)) {
                        elements.remove(key);
                    } else {
                        removeEntries.add(key);
                    }
                }

                if (removeEntries.isEmpty() && updateEntries.isEmpty()) {
                    baseTerms.add(setUpdate.set());
                } else {
                    baseTerms.add(new SetUpdate(setUpdate.set(), removeEntries, updateEntries));
                }
            }

            if (baseTerms.size() == 1 && elements.isEmpty()) {
                /* if the SetBuiltin instance consists of only one base term,
                 * return the base term instead */
                return baseTerms.get(0);
            } else {
                return new SetBuiltin(node.sort(), elements, baseTerms);
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
