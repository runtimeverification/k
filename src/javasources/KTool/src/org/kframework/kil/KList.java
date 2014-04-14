// Copyright (C) 2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.w3c.dom.Element;

import aterm.ATermAppl;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/** Represents a ,, list, as used in KApp */
public class KList extends Collection {

    public static final KList EMPTY = new KList(Collections.<Term> emptyList());

    public KList() {
        super(KSorts.KLIST);
    }

    public KList(String location, String filename) {
        super(location, filename, KSorts.KLIST);
    }

    public KList(Element element) {
        super(element);
    }

    public KList(ATermAppl atm) {
        super(atm);
    }

    public KList(KList node) {
        super(node);
    }

    public KList(List<Term> col) {
        super(KSorts.KLIST, col);
    }

    public KList(Term ... terms) { this(Arrays.asList(terms)); }

    @Override
    public String toString() {
        String content = "";
        for (int i = 0; i < contents.size(); i++) {
            if (i == contents.size() - 1)
                content += contents.get(i);
            else
                content += contents.get(i) + ",, ";
        }
        return content;
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        return transformer.transform(this);
    }

    @Override
    public void accept(Matcher matcher, Term toMatch) {
        matcher.match(this, toMatch);
    }

    @Override
    public KList shallowCopy() {
        return new KList(this);
    }

}
