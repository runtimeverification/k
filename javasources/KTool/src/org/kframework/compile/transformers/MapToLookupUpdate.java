package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.MapLookup;
import org.kframework.kil.MapUpdate;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;


/**
 * Transformer class compiling map accesses into lookup and update operations.
 *
 * @see MapLookup
 * @see MapUpdate
 *
 * @author AndreiS
 */
public class MapToLookupUpdate extends CopyOnWriteTransformer {

    private class ExtendedMapLookup extends MapLookup {
        public Set<Variable> variables;

        ExtendedMapLookup(Term key, Term value, Variable map) {
            super(map, key, value);
            variables = key.variables();
        }
    }

    private enum Status {LHS, RHS, CONDITION }

    private Map<Variable, MapUpdate> reverseMap = new HashMap<Variable, MapUpdate>();
    private ArrayList<ExtendedMapLookup> queue = new ArrayList<ExtendedMapLookup>();
    private Status status;

    public MapToLookupUpdate(Context context) {
        super("Compile maps into load and store operations", context);
    }

    @Override
    public ASTNode transform(Rule node) throws TransformerException {
        assert node.getBody() instanceof Rewrite:
               "expected rewrite at the top of rule " + node + ". "
               + "MapToLookupUpdate pass should be applied after ResolveRewrite pass.";

        reverseMap.clear();
        queue.clear();

        Rewrite rewrite = (Rewrite) node.getBody();
        status = Status.LHS;
        Term lhs = (Term) rewrite.getLeft().accept(this);

        List<MapLookup> lookups = new ArrayList<MapLookup>();

        for (ExtendedMapLookup item : queue) {
            item.variables.removeAll(lhs.variables());
        }

        boolean change;
        do {
            change = false;
            for (int i = 0; i < queue.size(); ++i) {
                if (queue.get(i).variables.isEmpty()) {
                    change = true;
                    MapLookup lookup = queue.remove(i);
                    lookups.add(new MapLookup(lookup.map(), lookup.key(), lookup.value()));

                    for (ExtendedMapLookup extendedLookup : queue) {
                        extendedLookup.variables.removeAll(lookup.value().variables());
                    }
                }
            }
        } while (change);

        if (!queue.isEmpty()) {
            /* TODO(AndreiS): handle iteration over maps */
            GlobalSettings.kem.register(new KException(
                    KException.ExceptionType.WARNING,
                    KException.KExceptionGroup.CRITICAL,
                    "Unsupported map pattern in the rule left-hand side",
                    node.getFilename(),
                    node.getLocation()));
            return node;
        }

        status = Status.RHS;
        Term rhs = (Term) rewrite.getRight().accept(this);
        Term condition = node.getCondition();
        if (condition != null) {
            status = Status.CONDITION;
            condition = (Term) condition.accept(this);
        }

        if (lhs == rewrite.getLeft() && rhs == rewrite.getRight()
                && condition == node.getCondition()) {
            return node;
        }

        Rule returnNode = node.shallowCopy();
        rewrite = rewrite.shallowCopy();
        rewrite.setLeft(lhs, context);
        rewrite.setRight(rhs, context);
        returnNode.setBody(rewrite);
        returnNode.setCondition(condition);
        returnNode.setLookups(lookups);
        return returnNode;
    }

    @Override
    public ASTNode transform(MapBuiltin node) throws TransformerException {
        node = (MapBuiltin) super.transform(node);
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
                /* TODO(AndreiS): check the uniqueness of map variables in the LHS */
                reverseMap.put(
                        node.viewBase(),
                        new MapUpdate(variable, node.elements(), Collections.<Term, Term>emptyMap()));
            }
            for (Map.Entry<Term, Term> entry : node.elements().entrySet()) {
                queue.add(new ExtendedMapLookup(entry.getKey(), entry.getValue(), variable));
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
    public ASTNode transform(Variable node) throws TransformerException {
        if (status != Status.LHS && reverseMap.containsKey(node)) {
            return reverseMap.get(node);
        } else {
            return node;
        }
    }

}
