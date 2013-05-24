package org.kframework.compile.sharing;

import org.kframework.kil.Attribute;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import com.google.common.collect.ImmutableMap;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


/**
 * Visitor collecting the names of the sorts with productions hooked to data structures (bag,
 * list, map or set). A sort may be hooked to only one data structure.
 *
 * @author AndreiS
 */
public class DataStructureSortCollector extends BasicVisitor {
    /* TODO: merge with the rest of the builtins */

    private Map<String, String> types = new HashMap<String, String>();
    private Map<String, String> constructorLabels = new HashMap<String, String>();
    private Map<String, String> elementLabels = new HashMap<String, String>();
    private Map<String, String> unitLabels = new HashMap<String, String>();
    private Map<String, Set<String>> operatorLabels = new HashMap<String, Set<String>>();

    public DataStructureSortCollector(Context context) {
        super(context);
    }

    public Map<String, DataStructureSort> getSorts() {
        ImmutableMap.Builder<String, DataStructureSort> builder = ImmutableMap.builder();
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

            DataStructureSort dataStructureSort = new DataStructureSort(
                    sort,
                    types.get(sort),
                    constructorLabels.get(sort),
                    elementLabels.get(sort),
                    unitLabels.get(sort),
                    operatorLabels.get(sort));
            builder.put(sort, dataStructureSort);
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
        if (!Context.DataStructureTypes.contains(type)) {
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

        Map<Context.DataStructureLabel, String> labels
                = Context.dataStructureLabels.get(type);
        if (operator.equals(labels.get(Context.DataStructureLabel.CONSTRUCTOR))) {
            if (constructorLabels.containsKey(sort)) {
                /* TODO: print error message */
                return;
            }

            constructorLabels.put(sort, node.getKLabel());
        } else if (operator.equals(labels.get(Context.DataStructureLabel.ELEMENT))) {
            if (elementLabels.containsKey(sort)) {
                /* TODO: print error message */
                return;
            }

            elementLabels.put(sort, node.getKLabel());
        } else if (operator.equals(labels.get(Context.DataStructureLabel.UNIT))) {
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
