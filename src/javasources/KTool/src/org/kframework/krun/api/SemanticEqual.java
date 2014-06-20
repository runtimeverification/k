// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.api;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.kframework.kil.BackendTerm;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Collection;
import org.kframework.kil.CollectionItem;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;

/*
 * Class used to check for semantic equality
 * The need for semantic equality comes from the fact that when using 
 * debugger step-all command multiples time on same node each time the 
 * symbolic stuffs will have new value in results. 
 * Here, for now, we take in consideration just cases where symbolic is used 
 * to generate fresh values for IntBuiltin      
 */
public class SemanticEqual {

    /*
     * used to mark that we should expect new/changed value
     */
    private static boolean store;
    /*
     * stores old,new value map
     */
    private static HashMap<String, String> replaceMap = new HashMap<>();
    /*
     * cache old results
     */
    private static ArrayList<Result> prevResults = new ArrayList<>();

    /*
     * Checks if the two terms are semantic equals
     */
    synchronized public static boolean checkEquality(Term t1, Term t2) {
        // first check if we already calculate equality for those terms
        for (Result r : prevResults) {
            if ((r.t1 == t1 && r.t2 == t2) || (r.t1 == t2 && r.t2 == t1))
                return r.result;
        }
        // clear previously calculated replacements
        replaceMap.clear();
        boolean result = areEqual(t1, t2);
        // store results for compared terms
        prevResults.add(new Result(t1, t2, result));
        replaceMap.clear();
        return result;
    }

    /*
     * Checks equality for two terms. Checks for Term instance and delegate to
     * specific method to check equality. As last resource use defined equals
     * method
     */
    private static boolean areEqual(Term t1, Term t2) {
        if (!checkForNull(t1, t2)) {
            return false;
        }
        // check if the instances are from the same class
        if (!t1.getClass().equals(t2.getClass())) {
            return false;
        }
        // here we know that the instances are from the same class
        else if (t1 instanceof BackendTerm) {
            // TODO check equality for BackendTerm
            return ((BackendTerm) t1).getValue().length() == ((BackendTerm) t2).getValue()
                    .length();
        } else if (t1 instanceof IntBuiltin) {
            return areEqual((IntBuiltin) t1, (IntBuiltin) t2);
        } else if (t1 instanceof KApp) {
            return areEqual((KApp) t1, (KApp) t2);
        } else if (t1 instanceof CollectionItem) {
            return areEqual((CollectionItem) t1, (CollectionItem) t2);
        } else if (t1 instanceof Collection) {
            return areEqual((Collection) t1, (Collection) t2);
        } else if (t1 instanceof Cell) {
            return areEqual((Cell) t1, (Cell) t2);
        } else if (t1 instanceof KInjectedLabel) {
            return areEqual((KInjectedLabel) t1, (KInjectedLabel) t2);
        }else if (t1 instanceof TermCons){
            return areEqual((TermCons) t1, (TermCons) t2);
        }
        return t1.equals(t2);
    }

    /*
     * Checks equals for two CollectionItem terms. Here we check if the items
     * from both instances are equal
     */
    private static boolean areEqual(CollectionItem c1, CollectionItem c2) {
        if (!checkForNull(c1, c2)) {
            return false;
        }
        return areEqual(c1.getItem(), c2.getItem());
    }

    /*
     * Checks equals for two KApp terms. Here we check if the labels and
     * children are equal
     */
    private static boolean areEqual(KApp k1, KApp k2) {
        if (!checkForNull(k1, k2)) {
            return false;
        }
        // check if we need to mark that we may expect new/changed value
        // if we already mark that we expect new value, preserve value
        // we want to check new/changed for symbolic stuffs
        store = k1.getLabel().toString().startsWith("#sym") || store;
        boolean rez = areEqual(k1.getLabel(), k2.getLabel())
                && areEqual(k1.getChild(), k2.getChild());
        // unmark
        store = false;
        return rez;
    }

    /*
     * Checks equals for two IntBuiltin terms. If we previously marked for
     * new/changed value store new mapped values or check if replacement
     * preserves.
     */
    private static boolean areEqual(IntBuiltin i1, IntBuiltin i2) {
        if (!checkForNull(i1, i2)) {
            return false;
        }
        if (store) {
            String prevValue = replaceMap.get(i1.value());
            if (prevValue == null) {
                // if no previous replacement occurred store new values
                replaceMap.put(i1.value(), i2.value());
                return true;
            } else {
                // check if replacement preserves
                boolean res = prevValue.equals(i2.value());
                return res;
            }
        }
        // if new/changed value was not marked, compare values of terms
        return i1.value().equals(i2.value());
    }

    /*
     * Checks if a collection is comutative 
     * BAG,SET,MAP are comuatative
     */
    private static boolean isComutative(Collection c){
        if(c instanceof Bag)
            return true;
        else {
            return false;
        }
    }
    
    /*
     * Checks equality for Collection terms. Check if sorts are equal and if
     * content lists are equal
     */
    private static boolean areEqual(Collection c1, Collection c2) {
        if (!checkForNull(c1, c2)) {
            return false;
        }
        if (!c1.getSort().equals(c2.getSort()))
            return false;
        if(isComutative(c1)){
            return areMultisetsEqual(c1.getContents(), c2.getContents());
        }
        else {
            return areSetsEqual(c1.getContents(), c2.getContents());
        }
    }

    /*
     * Checks equality for Cell terms. Check if sort, attributes, label and
     * contents are equal
     */
    private static boolean areEqual(Cell c1, Cell c2) {
        if (!checkForNull(c1, c2)) {
            return false;
        }
        if (!c1.getSort().equals(c2.getSort()))
            return false;
        if (!c1.getCellAttributes().equals(c2.getCellAttributes())) {
            return false;
        }
        if (!c1.getLabel().equals(c2.getLabel())) {
            return false;
        }
        return areEqual(c1.getContents(), c2.getContents())
                && areMultisetsEqual(c1.getCellTerms(), c2.getCellTerms());
    }

    /*
     * Checks equality for KInjectedLabel terms. Check wrapped terms are equal
     */
    private static boolean areEqual(KInjectedLabel k1, KInjectedLabel k2) {
        if (!checkForNull(k1, k2)) {
            return false;
        }
        return areEqual(k1.getTerm(), k2.getTerm());
    }

    /*
     * Checks equality for TermCons terms.
     */
    private static boolean areEqual(TermCons t1, TermCons t2) {
        if (!checkForNull(t1, t2)) {
            return false;
        }
        return areMultisetsEqual(t1.getContents(), t2.getContents());
    }
    
    /*
     * Check if both terms are null or not
     */
    private static boolean checkForNull(Object o1, Object o2) {
        if (o1 == null && o2 != null || o1 != null && o2 == null) {
            return false;
        }
        return true;
    }

    /*
     * Check if two lists contain same elements (ignoring elements order)
     */
    private static boolean areMultisetsEqual(List<Term> l1, List<Term> l2) {
        if (!checkForNull(l1, l2)) {
            return false;
        }
        if (l1.size() != l2.size())
            return false;
        // check if contents are equals (ignore order)
        // clone the list since we may remove items
        List<Term> clone = new ArrayList<>(l2);
        for (Term tt1 : l1) {
            int size = clone.size();
            for (int i = 0; i < size; i++) {
                if (areEqual(tt1, clone.get(i))) {
                    clone.remove(i);
                    break;
                }
            }
        }
        // for equality we should have removed all items
        return clone.isEmpty();
    }
    
    private static boolean areSetsEqual(List<Term> l1, List<Term> l2) {
        if (!checkForNull(l1, l2)) {
            return false;
        }
        if (l1.size() != l2.size())
            return false;
        // check if contents are equals
        for (int i = 0 ; i<l1.size();i++){
            if(!areEqual(l1.get(i), l2.get(i))){
                return false;
            }
        }
        // if we reach here the lists are equal since each l1(i) eqauls l2(i)
        return true;
    }
}

/*
 * Class used to store semantic equal result for two terms
 */
class Result {
    Term t1;
    Term t2;
    boolean result;

    public Result(Term t1, Term t2, boolean result) {
        super();
        this.t1 = t1;
        this.t2 = t2;
        this.result = result;
    }
}
