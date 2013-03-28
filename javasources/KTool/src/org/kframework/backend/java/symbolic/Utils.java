package org.kframework.backend.java.symbolic;


import java.util.ArrayList;
import java.util.ListIterator;

/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/24/13
 * Time: 4:57 PM
 * To change this template use File | Settings | File Templates.
 */
public class Utils {

    public static final ListIterator EMPTY_LIST_ITERATOR = (new ArrayList()).listIterator();

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

}
