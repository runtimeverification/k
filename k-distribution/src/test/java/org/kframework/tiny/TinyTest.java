package org.kframework.tiny;

import java.io.File;
import java.io.IOException;

import org.junit.Test;
import org.kframework.koreimplementation.convertors.BaseTest.DefintionWithContext;
import org.kframework.koreimplementation.convertors.KILtoKORE;
import org.kframework.koreimplementation.convertors.SDFCompilerTest;

public class TinyTest extends SDFCompilerTest {
    private static final String impMainModule = "IMP";

    private static final File impDefinitionFile = new File("tutorial/1_k/2_imp/lesson_1/imp.k");


    @Test public void imp() throws IOException {
        DefintionWithContext defWithContext = parse(impDefinitionFile.getAbsoluteFile(), impMainModule, true);
        KILtoKORE kilToKore = new KILtoKORE(defWithContext.context);
        org.kframework.definition.Definition koreDef = kilToKore.apply(defWithContext.definition);

        System.out.println(koreDef);
    }

//    private static final File impSimpleDefinitionFile = new File("src/test/resources/tiny-tests/imp.k");
//    @Test public void impOnNewParser() {
//        String mainModule = impMainModule;
//        Definition d = parseUsingOuter(
//                impSimpleDefinitionFile,
//                mainModule);
//        KILtoKORE kilToKore = new KILtoKORE(null);
//        org.kframework.definition.Definition koreDef = kilToKore.apply(d);
//
//        BubbleParsing bubbleParsing = new BubbleParsing();
//        Module koreModule = bubbleParsing.parseBubbles(koreDef.getModule(mainModule).get());
//
//        System.out.println(koreModule.toString());
//    }
//
//    private Definition parseUsingOuter(File file, String mainModule) {
//        Definition def = new Definition();
//        String definitionText;
//        try {
//            definitionText = FileUtils.readFileToString(file);
//        } catch (IOException e) {
//            throw new RuntimeException(e);
//        }
//        def.setItems(Outer.parse(Sources.generatedBy(TinyTest.class), definitionText, null));
//        def.setMainModule(mainModule);
//        def.setMainSyntaxModule(mainModule);
//        return def;
//    }
}
