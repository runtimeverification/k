package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.BuiltinLookup;
import org.kframework.kil.ListBuiltin;
import org.kframework.kil.ListLookup;
import org.kframework.kil.ListUpdate;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.MapLookup;
import org.kframework.kil.MapUpdate;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.SetBuiltin;
import org.kframework.kil.SetLookup;
import org.kframework.kil.SetUpdate;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;


/**
 * Transformer class compiling builtin data structure accesses into lookup and update operations.
 *
 * @see ListLookup
 * @see ListUpdate
 * @see MapLookup
 * @see MapUpdate
 * @see SetLookup
 * @see SetUpdate
 *
 * @author AndreiS
 */
public class DataStructureToLookupUpdate extends CopyOnWriteTransformer {

    private interface VariableCache {
        public Set<Variable> variables();
    }

    private class ExtendedListLookup extends ListLookup implements VariableCache {
        private Set<Variable> variables;

        ExtendedListLookup(Variable list, int key, Term value) {
            super(list, key, value);
            variables = new HashSet<Variable>();
            variables.add(list);
        }

        @Override
        public Set<Variable> variables() {
            return variables;
        }
    }

    private class ExtendedMapLookup extends MapLookup implements VariableCache {
        private Set<Variable> variables;

        ExtendedMapLookup(Variable map, Term key, Term value) {
            super(map, key, value);
            variables = new HashSet<Variable>();
            variables.add(map);
            variables.addAll(key.variables());
        }

        @Override
        public Set<Variable> variables() {
            return variables;
        }
    }

    private class ExtendedSetLookup extends SetLookup implements VariableCache {
        private Set<Variable> variables;

        ExtendedSetLookup(Variable set, Term key) {
            super(set, key);
            variables = new HashSet<Variable>();
            variables.add(set);
            variables.addAll(key.variables());
        }

        @Override
        public Set<Variable> variables() {
            return variables;
        }
    }

    private enum Status {LHS, RHS, CONDITION }

    private Map<Variable, Term> reverseMap = new HashMap<Variable, Term>();
    private Map<Variable, Integer> concreteSize = new HashMap<Variable, Integer>();
    private ArrayList<VariableCache> queue = new ArrayList<VariableCache>();
    private Status status;

    public DataStructureToLookupUpdate(Context context) {
        super("Compile maps into load and store operations", context);
    }

    @Override
    public ASTNode transform(Rule node) throws TransformerException {
        assert node.getBody() instanceof Rewrite:
               "expected rewrite at the top of rule " + node + ". "
               + "DataStructureToLookupUpdate pass should be applied after ResolveRewrite pass.";

        reverseMap.clear();
        concreteSize.clear();
        queue.clear();

        Rewrite rewrite = (Rewrite) node.getBody();
        status = Status.LHS;
        Term lhs = (Term) rewrite.getLeft().accept(this);

        List<BuiltinLookup> lookups = new ArrayList<BuiltinLookup>(node.getLookups());

        for (VariableCache item : queue) {
            item.variables().removeAll(lhs.variables());
        }

        boolean change;
        do {
            change = false;
            for (int i = 0; i < queue.size(); ++i) {
                if (queue.get(i).variables().isEmpty()) {
                    change = true;
                    VariableCache lookup = queue.remove(i);

                    if (lookup instanceof ListLookup) {
                        ListLookup listLookup = (ListLookup) lookup;
                        lookups.add(new ListLookup(
                                listLookup.base(),
                                listLookup.key(),
                                listLookup.value()));

                        for (VariableCache item : queue) {
                            item.variables().removeAll(listLookup.value().variables());
                        }
                    } else if (lookup instanceof MapLookup) {
                        MapLookup mapLookup = (MapLookup) lookup;
                        lookups.add(new MapLookup(
                                mapLookup.base(),
                                mapLookup.key(),
                                mapLookup.value()));

                        for (VariableCache item : queue) {
                            item.variables().removeAll(mapLookup.value().variables());
                        }
                    } else if (lookup instanceof SetLookup) {
                        SetLookup setLookup = (SetLookup) lookup;
                        lookups.add(new SetLookup(setLookup.base(), setLookup.key()));
                    } else {
                        assert false: "unexpected builtin data structure type";
                    }
                }
            }
        } while (change);

        if (!queue.isEmpty()) {
            /* TODO(AndreiS): handle iteration over builtin data structures */
            GlobalSettings.kem.register(new KException(
                    KException.ExceptionType.HIDDENWARNING,
                    KException.KExceptionGroup.CRITICAL,
                    "Unsupported map pattern in the rule left-hand side",
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
        //TODO: Handle Ensures as well.
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
        returnNode.setConcreteDataStructureSize(
                new HashMap<Variable, Integer>(returnNode.getConcreteDataStructureSize()));
        returnNode.getConcreteDataStructureSize().putAll(concreteSize);
        return returnNode;
    }

    @Override
    public ASTNode transform(ListBuiltin node) throws TransformerException {
        node = (ListBuiltin) super.transform(node);
        if (status == Status.LHS) {
            assert node.isLHSView();

            if (node.elementsLeft().isEmpty() && node.elementsRight().isEmpty()
                    && node.hasViewBase()) {
                return node.viewBase();
            }

            Variable variable = Variable.getFreshVar(node.sort().name());
            if (node.hasViewBase()) {
                /* TODO(AndreiS): check the uniqueness of list variables in the LHS */
                assert !reverseMap.containsKey(node.viewBase());

                reverseMap.put(
                        node.viewBase(),
                        new ListUpdate(variable, node.elementsLeft(), node.elementsRight()));
            } else {
                concreteSize.put(
                        variable,
                        node.elementsLeft().size() + node.elementsRight().size());
            }

            int key = 0;
            for (Term term : node.elementsLeft()) {
                queue.add(new ExtendedListLookup(variable, key, term));
                key++;
            }

            key = -node.elementsRight().size();
            for (Term term : node.elementsRight()) {
                queue.add(new ExtendedListLookup(variable, key, term));
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
                return ListBuiltin.of(node.sort(), elementsLeft, elementsRight, baseTerms);
            }
        }
    }

    @Override
    public ASTNode transform(MapBuiltin node) throws TransformerException {
        node = (MapBuiltin) super.transform(node);
        if (status == Status.LHS) {
            assert node.isLHSView();

            if (node.elements().isEmpty() && node.hasViewBase()) {
                    return node.viewBase();
            }

            Variable variable = Variable.getFreshVar(node.sort().name());
            if (node.hasViewBase()) {
                /* TODO(AndreiS): check the uniqueness of map variables in the LHS */
                assert !reverseMap.containsKey(node.viewBase());

                reverseMap.put(
                        node.viewBase(),
                        new MapUpdate(variable, node.elements(), Collections.<Term, Term>emptyMap()));
            } else {
                concreteSize.put(variable, node.elements().size());
            }

            for (Map.Entry<Term, Term> entry : node.elements().entrySet()) {
                queue.add(new ExtendedMapLookup(variable, entry.getKey(), entry.getValue()));
            }

            return variable;
        } else {
            /* status == Status.RHS || status == Status.CONDITION */
            List<Term> baseTerms = new ArrayList<Term>();
            Map<Term, Term> elements = new HashMap<Term, Term>(node.elements());
            for (Term term : node.baseTerms()) {
                if (!(term instanceof MapUpdate)) {
                    baseTerms.add(term);
                    continue;
                }
                MapUpdate mapUpdate = (MapUpdate) term;

                Map<Term, Term> removeEntries = new HashMap<Term, Term>();
                Map<Term, Term> updateEntries = new HashMap<Term, Term>();
                for (Map.Entry<Term, Term> entry : mapUpdate.removeEntries().entrySet()) {
                    if (elements.containsKey(entry.getKey())) {
                        if (elements.get(entry.getKey()).equals(entry.getValue())) {
                            elements.remove(entry.getKey());
                        } else {
                            updateEntries.put(entry.getKey(), elements.remove(entry.getKey()));
                        }
                    } else {
                        removeEntries.put(entry.getKey(), entry.getValue());
                    }
                }

                if (removeEntries.isEmpty() && updateEntries.isEmpty()) {
                    baseTerms.add(mapUpdate.map());
                } else {
                    baseTerms.add(new MapUpdate(mapUpdate.map(), removeEntries, updateEntries));
                }
            }

            if (baseTerms.size() == 1 && elements.isEmpty()) {
                /* if the MapBuiltin instance consists of only one base term,
                 * return the base term instead */
                return baseTerms.get(0);
            } else {
                return new MapBuiltin(node.sort(), elements, baseTerms);
            }
        }
    }

    @Override
    public ASTNode transform(SetBuiltin node) throws TransformerException {
        node = (SetBuiltin) super.transform(node);
        if (status == Status.LHS) {
            assert node.isLHSView();

            if (node.elements().isEmpty() && node.hasViewBase()) {
                return node.viewBase();
            }

            Variable variable = Variable.getFreshVar(node.sort().name());
            if (node.hasViewBase()) {
                /* TODO(AndreiS): check the uniqueness of map variables in the LHS */
                assert !reverseMap.containsKey(node.viewBase());

                reverseMap.put(
                        node.viewBase(),
                        new SetUpdate(variable, node.elements()));
            } else {
                concreteSize.put(variable, node.elements().size());
            }

            for (Term term : node.elements()) {
                queue.add(new ExtendedSetLookup(variable, term));
            }

            return variable;
        } else {
            /* status == Status.RHS || status == Status.CONDITION */
            List<Term> baseTerms = new ArrayList<Term>();
            Collection<Term> elements = new ArrayList<Term>(node.elements());
            for (Term term : node.baseTerms()) {
                if (!(term instanceof SetUpdate)) {
                    baseTerms.add(term);
                    continue;
                }
                SetUpdate setUpdate = (SetUpdate) term;

                Collection<Term> removeEntries = new ArrayList<Term>();
                for (Term key : setUpdate.removeEntries()) {
                    if (elements.contains(key)) {
                        elements.remove(key);
                    } else {
                        removeEntries.add(key);
                    }
                }

                if (removeEntries.isEmpty()) {
                    baseTerms.add(setUpdate.set());
                } else {
                    baseTerms.add(new SetUpdate(setUpdate.set(), removeEntries));
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
