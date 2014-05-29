// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.compile.sharing;

import org.kframework.kil.Attribute;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.HashMap;
import java.util.Map;

import com.google.common.collect.ImmutableMap;


/**
 * Visitor collecting the names of the sorts with productions hooked to data structures (bag,
 * list, map or set). A sort may be hooked to only one data structure.
 *
 * @author AndreiS
 */
public class DataStructureSortCollector extends BasicVisitor {
    /* TODO(AndreiS): merge with the rest of the builtins */

    private Map<String, String> types = new HashMap<String, String>();
    private Map<String, String> constructorLabels = new HashMap<String, String>();
    private Map<String, String> elementLabels = new HashMap<String, String>();
    private Map<String, String> unitLabels = new HashMap<String, String>();
    private Map<String, Map<String, String>> operatorLabels = new HashMap<String, Map<String, String>>();

    public DataStructureSortCollector(Context context) {
        super(context);
    }

    public Map<String, DataStructureSort> getSorts() {
        ImmutableMap.Builder<String, DataStructureSort> builder = ImmutableMap.builder();
        for (Map.Entry<String, String> entry : types.entrySet()) {
            String sort = entry.getKey();

            if (!types.containsKey(sort)) {
                /* TODO: print error message */
                continue;
            }
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
    public Void visit(Production node, Void _) {
        String sort = node.getSort();

        String hookAttribute = node.getAttribute(Attribute.HOOK_KEY);
        if (hookAttribute == null) {
            /* not a builtin */
            return null;
        }

        String[] strings = hookAttribute.split(":");
        if (strings.length != 2) {
            /* TODO: print error message */
            return null;
        }

        String type = strings[0];
        String operator = strings[1];
        if (!DataStructureSort.TYPES.contains(type)) {
            /* not a builtin collection */
            return null;
        }

        if (!operatorLabels.containsKey(sort)) {
            operatorLabels.put(sort, new HashMap<String, String>());
        }

        Map<DataStructureSort.Label, String> labels
                = DataStructureSort.LABELS.get(type);
        if (operator.equals(labels.get(DataStructureSort.Label.CONSTRUCTOR))) {
            if (constructorLabels.containsKey(sort)) {
                /* TODO: print error message */
                return null;
            }

            constructorLabels.put(sort, node.getKLabel());
        } else if (operator.equals(labels.get(DataStructureSort.Label.ELEMENT))) {
            if (elementLabels.containsKey(sort)) {
                /* TODO: print error message */
                return null;
            }

            elementLabels.put(sort, node.getKLabel());
        } else if (operator.equals(labels.get(DataStructureSort.Label.UNIT))) {
            if (unitLabels.containsKey(sort)) {
                /* TODO: print error message */
                return null;
            }

            unitLabels.put(sort, node.getKLabel());
        } else {
            /* domain specific function */
            operatorLabels.get(sort).put(operator, node.getKLabel());
        }

        /*
         * The type (list, map, set) of a data structure is determined by its constructor, element,
         * and unit
         */
        if (!operatorLabels.get(sort).containsKey(operator)) {
            if (types.containsKey(sort)) {
                if (!types.get(sort).equals(type)) {
                    /* TODO: print error message */
                    return null;
                }
            } else {
                types.put(sort, type);
            }
        }
        return null;
    }

}
