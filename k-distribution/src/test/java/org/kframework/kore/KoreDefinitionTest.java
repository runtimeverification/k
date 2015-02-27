// Copyright (c) 2015 K Team. All Rights Reserved.

package org.kframework.kore;

import org.apache.commons.io.IOUtils;
import static org.junit.Assert.assertEquals;
import org.junit.Test;
import static org.kframework.Collections.stream;
import org.kframework.kil.Sources;
import org.kframework.kore.convertors.BubbleParsing;
import org.kframework.kore.convertors.KILtoKORE;
import org.kframework.definition.*;
import org.kframework.parser.outer.Outer;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

/**
 * Basic testing of a complete definitions in kore syntax.
 * Parses bubbles as kore with the new parser, but currently uses the old parser
 * for the outer syntax because the new parser is not ready for that.
 */
public class KoreDefinitionTest {

    private final BubbleParsing bubbles = new BubbleParsing("K-TEST","RuleBody");

    public static void main(String[] args) throws Exception {
        Definition def = new KoreDefinitionTest().parse(new FileInputStream(args[0]));
        System.out.println(def);
    }

    @Test
    public void testSIMPLE1() {
        Definition def = parse(KoreDefinitionTest.class.getResourceAsStream("/kore/simple-untyped-1.kore"));
        // mostly just care that it parses, check a few counts for a tiny bit of sanity-checking.
        assertEquals(9, stream(def.modules()).count());
        assertEquals(323, stream(def.modules()).flatMap(m -> stream(m.localSentences())).count());
    }

    // TODO(radu): generalize this function, and eliminate duplicates
    private Definition parse(InputStream definition) {
        return bubbles.parseBubbles(outerParse(definition));
    }

    // TODO(radu): generalize this function, and eliminate duplicates
    private static Definition outerParse(InputStream definition) {
        org.kframework.kil.Definition def = new org.kframework.kil.Definition();
        String definitionText;
        try {
            definitionText = IOUtils.toString(definition);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        def.setItems(Outer.parse(Sources.generatedBy(KoreDefinitionTest.class), definitionText, null));
        def.setMainModule("SIMPLE-UNTYPED");
        def.setMainSyntaxModule("SIMPLE-UNTYPED-SYNTAX");

        KILtoKORE kilToKore = new KILtoKORE(null);
        Definition koreDef = kilToKore.apply(def);

        return koreDef;
    }
}