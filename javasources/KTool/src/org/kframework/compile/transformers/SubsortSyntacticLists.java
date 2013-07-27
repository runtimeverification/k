package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.KSorts;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sort;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;


/**
 * Completes the sort lattice for syntactic lists as follows:
 * 1. adds a bottom sort #Bot;
 * 2. adds a syntactic production List{#Bot, separator}, for each syntactic list separator;
 * 3. subsorts List{Sort1, separator} to List{Sort2, separator} if Sort1 is subsorted to Sort2; and
 * 4. subsorts List{Sort, separator} to KResult if Sort is subsorted to KResult
 *
 * The fields of the associated {@link Context} instance are not updated.
 *
 * @author AndreiS
 */
public class SubsortSyntacticLists extends CopyOnWriteTransformer {

    public static final String LIST_OF_BOTTOM_PREFIX = "#ListOfBot";
    public static final String BOTTM_SORT_NAME = "#Bot";

    public SubsortSyntacticLists(Context context) {
        super("Subsort syntactic lists", context);
    }

    public static String getListOfBottomSortName(String separator) {
        return SubsortSyntacticLists.LIST_OF_BOTTOM_PREFIX + "{\"" + separator + "\"}";
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
        Module transformedNode = node.shallowCopy();
        transformedNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        Set<String> separators = new HashSet<String>();

        /*
         * Subsort one syntactic list to another syntactic list with the same separator if the
         * sort of the elements of the first list is subsorted to the sort of the elements of the
         * second list (i.e. List{Sort1, separator} < List{Sort2, separator} if Sort1 < Sort2)
         */
        for (Production production1 : context.listConses.values()) {
            UserList userList1 = (UserList) production1.getItems().get(0);

            separators.add(userList1.getSeparator());

            for (Production production2 : context.listConses.values()) {
                UserList userList2 = (UserList) production2.getItems().get(0);

                if (userList1.getSeparator().equals(userList2.getSeparator())) {
                    if (context.isSubsorted(userList1.getSort(), userList2.getSort())) {
                        transformedNode.addSubsort(production1.getSort(), production2.getSort());
                    }
                }
            }
        }

        /* Add bottom sort #Bot */
        transformedNode.addProduction(
                SubsortSyntacticLists.BOTTM_SORT_NAME,
                new Production(
                        new Sort(SubsortSyntacticLists.BOTTM_SORT_NAME),
                        Collections.<ProductionItem>emptyList()));

        /* Add list of bottom for each syntactic list separator (i.e. List{#Bot, separator}) */
        for (String separator : separators) {
            transformedNode.addProduction(
                    SubsortSyntacticLists.getListOfBottomSortName(separator),
                    new UserList(SubsortSyntacticLists.BOTTM_SORT_NAME, separator));
        }

        /*
         * Subsort list of bottom to each syntactic list with the same separator
         * (i.e. List{#Bot, separator} < List{Sort, separator})
         */
        for (Production production : context.listConses.values()) {
            UserList userList = (UserList) production.getItems().get(0);
            transformedNode.addSubsort(
                    production.getSort(),
                    SubsortSyntacticLists.getListOfBottomSortName(userList.getSeparator()));
        }

        /*
         * Subsort a syntactic list to KResult if the sort of the elements of the list is
         * subsorted to KResult (i.e. List{Sort, separator} < KResult if Sort < KResult)
         */
        for (Production production : context.listConses.values()) {
            UserList userList = (UserList) production.getItems().get(0);

            if (context.isSubsorted(KSorts.KRESULT, userList.getSort())) {
                transformedNode.addSubsort(KSorts.KRESULT, production.getSort());
            }
        }


        if (transformedNode.getItems().size() != node.getItems().size()) {
            return transformedNode;
        } else {
            return node;
        }
    }

}
