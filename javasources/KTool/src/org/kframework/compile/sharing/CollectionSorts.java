package org.kframework.compile.sharing;

import org.kframework.kil.Attribute;
import org.kframework.kil.CollectionSort;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import com.google.common.collect.ImmutableMap;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


/**
 * Visitor collecting the names of the collection sorts.
 *
 * @author AndreiS
 */
public class CollectionSorts extends BasicVisitor {
    /* TODO: merge with the rest of the builtins */

    private Map<String, String> types = new HashMap<String, String>();
    private Map<String, String> constructorLabels = new HashMap<String, String>();
    private Map<String, String> elementLabels = new HashMap<String, String>();
    private Map<String, String> unitLabels = new HashMap<String, String>();
    private Map<String, Set<String>> operatorLabels = new HashMap<String, Set<String>>();

    public CollectionSorts(Context context) {
        super(context);
    }

    public Map<String, CollectionSort> getCollectionSorts() {
        ImmutableMap.Builder<String, CollectionSort> builder = ImmutableMap.builder();
        for (Map.Entry<String, String> entry : types.entrySet()) {
            String sort = entry.getKey();

            if (!constructorLabels.containsKey(sort)) {
                /* TODO: print error message */
                continue;
            }
            if (!elementLabels.containsKey(sort)) {
                /* TODO: print error message */
                continue;
            }
            if (!unitLabels.containsKey(sort)) {
                /* TODO: print error message */
                continue;
            }

            CollectionSort collectionSort = new CollectionSort(
                    sort,
                    types.get(sort),
                    constructorLabels.get(sort),
                    elementLabels.get(sort),
                    unitLabels.get(sort),
                    operatorLabels.get(sort));
            builder.put(sort, collectionSort);
        }

        return builder.build();
    }

    @Override
    public void visit(Production node) {
        String sort = node.getSort();

        String hookAttribute = node.getAttribute(Attribute.HOOK_KEY);
        if (hookAttribute == null) {
            /* not a builtin */
            return;
        }

        String[] strings = hookAttribute.split(":");
        if (strings.length != 2) {
            /* TODO: print error message */
            return;
        }

        String type = strings[0];
        String operator = strings[1];
        if (!Context.builtinCollectionTypes.contains(type)) {
            /* not a builtin collection */
            return;
        }

        if (types.containsKey(sort)) {
            if (!types.get(sort).equals(type)) {
                /* TODO: print error message */
                return;
            }
        } else {
            types.put(sort, type);
            operatorLabels.put(sort, new HashSet<String>());
        }

        Map<Context.BuiltinCollectionLabel, String> labels
                = Context.collectionLabels.get(type);
        if (operator.equals(labels.get(Context.BuiltinCollectionLabel.CONSTRUCTOR))) {
            if (constructorLabels.containsKey(sort)) {
                /* TODO: print error message */
                return;
            }

            constructorLabels.put(sort, node.getKLabel());
        } else if (operator.equals(labels.get(Context.BuiltinCollectionLabel.ELEMENT))) {
            if (elementLabels.containsKey(sort)) {
                /* TODO: print error message */
                return;
            }

            elementLabels.put(sort, node.getKLabel());
        } else if (operator.equals(labels.get(Context.BuiltinCollectionLabel.UNIT))) {
            if (unitLabels.containsKey(sort)) {
                /* TODO: print error message */
                return;
            }

            unitLabels.put(sort, node.getKLabel());
        } else {
            /* domain specific function */
            operatorLabels.get(sort).add(operator);
        }

    }

}
