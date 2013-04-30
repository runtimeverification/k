package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.kil.Production;
import org.kframework.kil.loader.DefinitionHelper;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/24/13
 * Time: 4:57 PM
 * To change this template use File | Settings | File Templates.
 */
public class Utils {

    public static final ListIterator EMPTY_LIST_ITERATOR = Collections.EMPTY_LIST.listIterator();

    public static final int HASH_PRIME = 47;

    public static String sortToKind(String sort) {
        if (sort.equals("BuiltinConstant")
                || sort.equals("Cell")
                || sort.equals("CellCollection")
                || sort.equals("K")
                || sort.equals("KLabel")
                || sort.equals("KList")
                || sort.equals("KSequence")
                || sort.equals("Map")) {
            return sort;
        } else {
            return "K";
        }
    }

    @SuppressWarnings("unchecked")
    public static List<Production> productionsOf(KLabel kLabel) {
        if (!(kLabel instanceof KLabelConstant)) {
            return (List<Production>) Collections.EMPTY_LIST;
        }
        KLabelConstant kLabelConstant = (KLabelConstant) kLabel;

        return Utils.productionsOf(kLabelConstant.getLabel());
    }

    @SuppressWarnings("unchecked")
    public static List<Production> productionsOf(String label) {
        Set<String> conses = DefinitionHelper.labels.get(label);
        if (conses == null) {
            return (List<Production>) Collections.EMPTY_LIST;
        }

        ArrayList<Production> productions = new ArrayList<Production>();
        for (String cons : conses) {
            assert DefinitionHelper.conses.containsKey(cons);

            productions.add(DefinitionHelper.conses.get(cons));
        }

        return productions;
    }

}
