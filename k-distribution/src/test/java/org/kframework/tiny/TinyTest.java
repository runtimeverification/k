package org.kframework.tiny;

import java.io.File;
import java.io.IOException;

import org.apache.commons.io.FileUtils;
import org.junit.Test;
import org.kframework.kil.Definition;
import org.kframework.kil.Sources;
import org.kframework.kore.convertors.BubbleParsing;
import org.kframework.kore.convertors.KILtoKORE;
import org.kframework.kore.outer.Module;
import org.kframework.parser.outer.Outer;

public class TinyTest {
    @Test public void imp() {
        String mainModule = "IMP";
        Definition d = parseUsingOuter(
                new File("src/test/resources/tiny-tests/imp.k"),
                mainModule);
        KILtoKORE kilToKore = new KILtoKORE(null);
        org.kframework.kore.outer.Definition koreDef = kilToKore.apply(d);

        BubbleParsing bubbleParsing = new BubbleParsing();
        Module koreModule = bubbleParsing.parseBubbles(koreDef.getModule(mainModule).get());

        System.out.println(koreModule.toString());
    }

    private Definition parseUsingOuter(File file, String mainModule) {
        Definition def = new Definition();
        String definitionText;
        try {
            definitionText = FileUtils.readFileToString(file);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        def.setItems(Outer.parse(Sources.generatedBy(TinyTest.class), definitionText, null));
        def.setMainModule(mainModule);
        def.setMainSyntaxModule(mainModule);
        return def;
    }
}
