// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.generator;

import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Sentence;
import org.kframework.definition.Terminal;
import org.kframework.kore.convertors.KOREtoKIL;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Class to hold easy to access information about user defined lists.
 */
public class UserList {
    public String sort = "";
    public String childSort = null;
    public String separator = null;
    public String terminatorKLabel = null;
    public String klabel = null;
    public boolean nonEmpty = false;
    public Production pList = null, pTerminator = null;
    public org.kframework.attributes.Att attrs = null;

    // find all productions annotated with 'userList'
    // expecting to always find 2 of them of the form:
    // Es ::= E "," Es  [right, userList, klabel(...)]
    // Es ::= ".Es"     [userList, klabel(...)]
    public static java.util.List<UserList> getLists(Set<Sentence> sentences) {
        Map<Boolean, List<Sentence>> separatedProds
                = sentences.stream().collect(Collectors.groupingBy(p -> p instanceof Production && p.att().contains(KOREtoKIL.USER_LIST_ATTRIBUTE)));
        Map<String, java.util.List<Sentence>> listsMap = separatedProds.getOrDefault(true, new LinkedList<>())
                .stream().collect(Collectors.groupingBy(s -> ((Production) s).sort().name()));

        java.util.List<UserList> res = new ArrayList<>();
        for (Map.Entry<String, java.util.List<Sentence>> x : listsMap.entrySet()) {
            UserList ul = new UserList();
            ul.sort = x.getKey();
            assert x.getValue().size() == 2;
            for (Sentence s : x.getValue()) {
                Production p = (Production) s;
                if (p.items().size() == 3) {
                    Terminal t = (Terminal) p.items().tail().head();
                    ul.separator = t.value();
                    ul.klabel = p.klabel().get().name();
                    ul.attrs = p.att().remove("klabel");
                    ul.nonEmpty = ul.attrs.get(KOREtoKIL.USER_LIST_ATTRIBUTE).get().equals("+");
                    ul.childSort = ((NonTerminal) p.items().head()).sort().name();
                    ul.pList = p;
                } else if (p.items().size() == 1 && p.items().head() instanceof Terminal) {
                    ul.terminatorKLabel = p.klabel().get().name();
                    ul.pTerminator = p;
                } else
                    throw new AssertionError("Didn't expect this type of production when recognizing userList patterns!");
            }
            assert ul.attrs != null;
            assert ul.klabel != null;
            assert ul.terminatorKLabel != null;
            assert ul.childSort != null;
            res.add(ul);
        }
        return res;
    }
}
