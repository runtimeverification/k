// Copyright (c) 2014 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import org.junit.Test;

import static org.junit.Assert.*;

import org.kframework.kil.Sources;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kore.outer.Definition;
import org.kframework.parser.outer.Outer;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class TestKOREtoKILIT extends BaseTest {

    static final String ROOT = "src/test/resources/reverse-convertor-tests/";

    @Test
    public void testConfiguration() throws IOException {
        org.kframework.kil.Definition kilDef = parse(
                new File(ROOT + "configuration.k").getAbsoluteFile(), "TEST");

        KILtoKORE toKore = new KILtoKORE();
        org.kframework.kore.outer.Definition koreDef = toKore.apply(kilDef);

        KOREtoKIL toKil = new KOREtoKIL();
        org.kframework.kil.Definition kilDef1 = toKil.convertDefinition(koreDef);
    }

    @Test
    public void testRules() throws IOException {
        org.kframework.kil.Definition kilDef = parse(
                new File(ROOT + "syntaxWithOR.k").getAbsoluteFile(), "TEST");

        KILtoKORE toKore = new KILtoKORE();
        org.kframework.kore.outer.Definition koreDef = toKore.apply(kilDef);

        KOREtoKIL toKil = new KOREtoKIL();
        org.kframework.kil.Definition kilDef1 = toKil.convertDefinition(koreDef);
    }

    @Test
    public void testBubble() {
        String pgm = "module PGM " +
                "configuration <k> .K </k> " +
                "endmodule";
        org.kframework.kil.Definition kilDef = parseAndTranslateBack(pgm);

        List<String> sentences = new ArrayList<>();
        BasicVisitor variableCollector = new BasicVisitor(null) {
            @Override
            public Void visit(org.kframework.kil.StringSentence string, Void _void) {
                sentences.add(string.getContent());
                return _void;
            }
        };
        variableCollector.visitNode(kilDef);
        assertEquals(sentences.size(), 1);
        assertEquals(sentences.get(0), "<k> .K </k>");
    }

    @Test
    public void testListConversion() {
        String pgm = "module PGM " +
                "syntax UserLst ::= List{Elem, \",\"} " +
                "syntax NotYourUsualList ::= UserLst " +
                "syntax AnotherList ::= List{Elem2, \"!\"} " +
                "endmodule";
        org.kframework.kil.Definition kilDef = parseAndTranslateBack(pgm);

        final int[] lists = {0};
        BasicVisitor variableCollector = new BasicVisitor(null) {
            @Override
            public Void visit(org.kframework.kil.UserList lst, Void _void) {
                lists[0]++;
                return _void;
            }
        };
        variableCollector.visitNode(kilDef);
        assertEquals(lists[0], 2);
    }

    public org.kframework.kil.Definition parseAndTranslateBack(String pgm) {
        org.kframework.kil.Definition kilDef = new org.kframework.kil.Definition();
        kilDef.setItems(Outer.parse(Sources.generatedBy(TestKOREtoKILIT.class), pgm, null));

        KILtoKORE toKore = new KILtoKORE();
        Definition koreDef = toKore.apply(kilDef);
        KOREtoKIL toKil = new KOREtoKIL();
        org.kframework.kil.Definition kilDef1 = toKil.convertDefinition(koreDef);

        return kilDef1;
    }
}
