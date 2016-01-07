// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.definition;

import org.kframework.attributes.Att;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Sentence;
import org.kframework.definition.Terminal;

import java.util.*;
import java.util.stream.Collectors;

import org.kframework.Collections;

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

    public static scala.collection.Set<UserList> apply(scala.collection.Set<Sentence> sentences) {
        return Collections.immutable(getLists(Collections.mutable(sentences))).toSet();
    }

    // find all productions annotated with 'userList'
    // expecting to always find 2 of them of the form:
    // Es ::= E "," Es  [right, userList, klabel(...)]
    // Es ::= ".Es"     [userList, klabel(...)]
    public static java.util.List<UserList> getLists(Set<Sentence> sentences) {
        Map<Boolean, List<Sentence>> separatedProds
                = sentences.stream().collect(Collectors.groupingBy(p -> p instanceof Production && p.att().contains(Att.userList())));
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
                    // should work without the Att.userList() att, i.e. for any list -- see #1892
                    ul.nonEmpty = ul.attrs.get(Att.userList()).get().equals("+");
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
