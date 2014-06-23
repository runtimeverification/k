// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.KSorts;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sort;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.AddConsesVisitor;
import org.kframework.kil.loader.CollectConsesVisitor;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * Completes the sort lattice as follows:
 * 1. adds a bottom sort #Bot;
 * 2. adds a syntactic production List{#Bot, separator}, for each syntactic list separator;
 * 3. subsorts Sort1 to Sort2 if all subsorts of Sort1 are subsorts of Sort2 and Sort1 only
 *    contains subsorting productions;
 * 4. adds List{Sort2, separator} if List{Sort1, separator} and Sort2 < Sort1
 * 5. subsorts List{Sort1, separator} to List{Sort2, separator} if Sort1 is subsorted to Sort2
 * 6. subsorts List{#Bot, separator} to List{Sort, separator}; and
 * 7. subsorts List{Sort, separator} to KResult if Sort is subsorted to KResult
 *
 * Does NOT support syntactic lists of syntactic lists.
 * Supports at most ONE syntactic list for each sort and separator.
 *
 * The fields of the associated {@link Context} instance may not be updated.
 *
 * @author AndreiS
 */
public class CompleteSortLatice extends CopyOnWriteTransformer {

    public static final String LIST_OF_BOTTOM_PREFIX = "#ListOf";
    public static final String BOTTOM_SORT_NAME = "#Bot";

    public CompleteSortLatice(Context context) {
        super("Subsort syntactic lists", context);
    }

    public static String getUserListName(String sort, String separator) {
        return CompleteSortLatice.LIST_OF_BOTTOM_PREFIX + sort + "{\"" + separator + "\"}";
    }

    @Override
    public ASTNode visit(Module node, Void _)  {
        Module transformedNode = node.shallowCopy();
        transformedNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        Set<String> separators = new HashSet<String>();
        for (Production production : context.listConses.values()) {
            UserList userList = (UserList) production.getItems().get(0);
            separators.add(userList.getSeparator());
        }

        /* Add bottom sort #Bot */
        transformedNode.addProduction(
                CompleteSortLatice.BOTTOM_SORT_NAME,
                new Production(
                        new Sort(CompleteSortLatice.BOTTOM_SORT_NAME),
                        Collections.<ProductionItem>emptyList()));

        /* Add list of bottom for each syntactic list separator (i.e. List{#Bot, separator}) */
        for (String separator : separators) {
            transformedNode.addProduction(
                    CompleteSortLatice.getUserListName(
                            CompleteSortLatice.BOTTOM_SORT_NAME,
                            separator),
                    new UserList(CompleteSortLatice.BOTTOM_SORT_NAME, separator));
        }

        /*
         * Subsorts Sort1 to Sort2 if all productions of Sort1 are subsorting of sorts which are
         * also subsorts of Sort2 (i.e. Sort1 < Sort2 if syntax Sort1 ::= Sort3 and Sort3 < Sort2
         * for each production of Sort1).
         */
        boolean change;
        do {
            change = false;

        sort1_loop:
            for (String sort1 : node.getAllSorts()) {
                Collection<Production> productions = node.getProductionsOf(sort1);
                if (productions.isEmpty()) {
                    continue;
                }

                for (Production production : productions) {
                    if (!production.isSubsort()) {
                        continue sort1_loop;
                    }
                }

            sort2_loop:
                for (String sort2 : node.getAllSorts()) {
                    // TODO(AndreiS): deal with equivalent sorts
                    if (context.isSubsortedEq(sort2, sort1) || context.isSubsortedEq(sort1, sort2)
                            || context.isListSort(sort2)) {
                        continue;
                    }

                    for (Production production : productions) {
                        if (!context.isSubsorted(sort2, production.getChildSort(0))) {
                            continue sort2_loop;
                        }
                    }

                    transformedNode.addSubsort(sort2, sort1, context);
                    change = true;
                }
            }

            // TODO(AndreiS): subsort queries should implement lazy subsort computation
            context.computeSubsortTransitiveClosure();
        } while (change);

        /*
         * Add list of Sort2 for a separator it there is some syntactic list of Sort1 with the
         * same separator such that Sort2 is a subsort of Sort1
         * (i.e. List{Sort2, separator} if List{Sort1, separator} and Sort2 < Sort1)
         */
        for (Production production1 : context.listConses.values()) {
            UserList userList1 = (UserList) production1.getItems().get(0);

            Set<String> subsorts = new HashSet<String>();
            for (Production production2 : context.listConses.values()) {
                UserList userList2 = (UserList) production2.getItems().get(0);

                if (userList1.getSeparator().equals(userList2.getSeparator())) {
                    if (context.isSubsorted(userList1.getSort(), userList2.getSort())) {
                        subsorts.add(userList2.getSort());
                    }
                }
            }

            for (String sort : node.getAllSorts()) {
                if (!subsorts.contains(sort) && context.isSubsorted(userList1.getSort(), sort)) {
                    transformedNode.addProduction(
                            CompleteSortLatice.getUserListName(sort, userList1.getSeparator()),
                            new UserList(sort, userList1.getSeparator()));
                }
            }
        }
        /* add conses to new syntactic lists */
        new AddConsesVisitor(context).visitNode(transformedNode);
        /* update syntactic lists conses information in the context */
        new CollectConsesVisitor(context).visitNode(transformedNode);

        /*
         * Subsort one syntactic list to another syntactic list with the same separator if the
         * sort of the elements of the first list is subsorted to the sort of the elements of the
         * second list (i.e. List{Sort1, separator} < List{Sort2, separator} if Sort1 < Sort2)
         */
        for (Production production1 : context.listConses.values()) {
            UserList userList1 = (UserList) production1.getItems().get(0);

            for (Production production2 : context.listConses.values()) {
                UserList userList2 = (UserList) production2.getItems().get(0);

                if (userList1.getSeparator().equals(userList2.getSeparator())) {
                    if (context.isSubsorted(userList1.getSort(), userList2.getSort())) {
                        transformedNode.addSubsort(
                                production1.getSort(),
                                production2.getSort(),
                                context);
                    }
                }
            }
        }

        /*
         * Subsort list of bottom to each syntactic list with the same separator
         * (i.e. List{#Bot, separator} < List{Sort, separator})
         */
        for (Production production : context.listConses.values()) {
            UserList userList = (UserList) production.getItems().get(0);

            if (userList.getSort().equals(CompleteSortLatice.BOTTOM_SORT_NAME)) {
                continue;
            }

            transformedNode.addSubsort(
                    production.getSort(),
                    CompleteSortLatice.getUserListName(
                            CompleteSortLatice.BOTTOM_SORT_NAME,
                            userList.getSeparator()),
                    context);
        }

        /*
         * Subsort a syntactic list to KResult if the sort of the elements of the list is
         * subsorted to KResult (i.e. List{Sort, separator} < KResult if Sort < KResult)
         */
        for (Production production : context.listConses.values()) {
            UserList userList = (UserList) production.getItems().get(0);

            if (context.isSubsorted(KSorts.KRESULT, userList.getSort())) {
                transformedNode.addSubsort(KSorts.KRESULT, production.getSort(), context);
            }
        }

        if (transformedNode.getItems().size() != node.getItems().size()) {
            return transformedNode;
        } else {
            return node;
        }
    }

}
