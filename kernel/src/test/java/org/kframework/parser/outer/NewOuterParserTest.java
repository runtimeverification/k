package org.kframework.parser.outer;

import org.apache.commons.io.FileUtils;
import org.junit.Test;
import org.kframework.kil.Definition;
import org.kframework.kil.Sources;
import org.kframework.koreimplementation.K;
import org.kframework.koreimplementation.convertors.KILtoKORE;
import org.kframework.definition.Module;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Term;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.Grammar;
import org.kframework.parser.concrete2kore.KSyntax2GrammarStatesFilter;
import org.kframework.parser.concrete2kore.Parser;
import org.kframework.parser.concrete2kore.TreeCleanerVisitor;

import java.io.File;
import java.io.IOException;

/**
 * Tests the K definition of the outer K syntax.
 */
public class NewOuterParserTest {

    @Test
    public void testKOREOuter() throws Exception {
        CharSequence theTextToParse = "module FOO endmodule";
        String mainModule = "KORE";
        String startSymbol = "KDefinition";
        File definitionFile = new File("k-distribution/src/test/resources/convertor-tests/koreimplementation.k").getAbsoluteFile();

        K kBody = parseWithFile(theTextToParse, mainModule, startSymbol, definitionFile);
        System.out.println(kBody);
    }

    /**
     * @param theTextToParse
     * @param mainModule
     * @param startSymbol
     * @param definitionFile
     * @return
     */
    private K parseWithFile(CharSequence theTextToParse, String mainModule, String startSymbol, File definitionFile) {
        Definition def = new Definition();
        String definitionText;
        try {
            definitionText = FileUtils.readFileToString(definitionFile);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        def.setItems(Outer.parse(Sources.generatedBy(NewOuterParserTest.class), definitionText, null));
        def.setMainModule(mainModule);
        def.setMainSyntaxModule(mainModule);

        KILtoKORE kilToKore = new KILtoKORE(null);
        org.kframework.definition.Definition koreDef = kilToKore.apply(def);

        Module kastModule = koreDef.getModule(mainModule).get();

        Grammar kastGrammar = KSyntax2GrammarStatesFilter.getGrammar(kastModule);

        Parser parser = new Parser(theTextToParse);
        Term parsed = parser.parse(kastGrammar.get(startSymbol), 0);

        if (parsed.equals(Ambiguity.apply())) {
            Parser.ParseError errors = parser.getErrors();
            throw new AssertionError("There are parsing errors: " + errors.toString());
        }

        TreeCleanerVisitor treeCleanerVisitor = new TreeCleanerVisitor();
        Term cleaned = treeCleanerVisitor.apply(parsed).right().get();

        return TreeNodesToKORE.apply(cleaned);
    }
}
