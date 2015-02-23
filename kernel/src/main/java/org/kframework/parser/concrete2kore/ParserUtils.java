// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import org.apache.commons.io.FileUtils;
import org.kframework.kil.Definition;
import org.kframework.kil.Sources;
import org.kframework.kore.K;
import org.kframework.kore.convertors.KILtoKORE;
import org.kframework.kore.outer.Module;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Term;
import org.kframework.parser.TreeNodesToKORE;
import org.kframework.parser.concrete2kore.disambiguation.PreferAvoidVisitor;
import org.kframework.parser.concrete2kore.disambiguation.PriorityVisitor;
import org.kframework.parser.concrete2kore.disambiguation.TreeCleanerVisitor;
import org.kframework.parser.concrete2kore.kernel.Grammar;
import org.kframework.parser.concrete2kore.kernel.KSyntax2GrammarStatesFilter;
import org.kframework.parser.concrete2kore.kernel.Parser;
import org.kframework.parser.outer.Outer;

import java.io.File;
import java.io.IOException;

/**
 * A few functions that are a common pattern when calling the new parser.
 */
public class ParserUtils {

    public static K parseWithFile(CharSequence theTextToParse, String mainModule, String startSymbol, File definitionFile) {
        String definitionText;
        try {
            definitionText = FileUtils.readFileToString(definitionFile);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        return parseWithString(theTextToParse, mainModule, startSymbol, definitionText);
    }

    public static K parseWithString(CharSequence theTextToParse, String mainModule, String startSymbol, String definitionText) {
        Definition def = new Definition();
        def.setItems(Outer.parse(Sources.generatedBy(ParserUtils.class), definitionText, null));
        def.setMainModule(mainModule);
        def.setMainSyntaxModule(mainModule);

        KILtoKORE kilToKore = new KILtoKORE(null);
        org.kframework.kore.outer.Definition koreDef = kilToKore.apply(def);
        Module kastModule = koreDef.getModule(mainModule).get();
        return parseWithModule(theTextToParse, startSymbol, kastModule);
    }

    public static K parseWithModule(CharSequence theTextToParse, String startSymbol, org.kframework.kore.outer.Module kastModule) {
        ParseInModule parser = new ParseInModule(kastModule);
        Term cleaned = parser.parseString(theTextToParse, startSymbol);
        return TreeNodesToKORE.apply(cleaned);
    }
}
