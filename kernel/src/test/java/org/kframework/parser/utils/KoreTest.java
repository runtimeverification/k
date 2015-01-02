// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.utils;

import org.apache.commons.io.FileUtils;
import org.junit.Test;
import org.kframework.compile.sharing.TokenSortCollector;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.GeneratedSource;
import org.kframework.kil.Module;
import org.kframework.kil.ProductionReference;
import org.kframework.kil.Sort;
import org.kframework.kil.Sources;
import org.kframework.kil.loader.CollectPrioritiesVisitor;
import org.kframework.kil.loader.CollectSubsortsVisitor;
import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.FillInModuleContext;
import org.kframework.kil.loader.UpdateReferencesVisitor;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.ProgramLoader;
import org.kframework.parser.concrete2.Grammar;
import org.kframework.parser.concrete2.KSyntax2GrammarStatesFilter;
import org.kframework.parser.generator.CollectTerminalsVisitor;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.BaseTestCase;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;

import java.io.File;
import java.util.Set;

/**
 * Test a the kore definition using the new parser.
 * KoreTest has to be run after the distribution has been built (apparently), therefore the name IT at the end.
 */
public class KoreTest extends BaseTestCase {

    @Test
    public void testKore() throws Exception {
        String quq = FileUtils.readFileToString(new File(getClass().getResource("/kast/quote-unquote.kore").toURI()));
        String kore = FileUtils.readFileToString(new File(getClass().getResource("/kast/kore.k").toURI()));
        Definition def = new Definition();
        def.setItems(Outer.parse(Sources.generatedBy(KoreTest.class), kore, null));
        def.setMainModule(((Module) def.getItems().get(def.getItems().size() - 1)).getName());
        ProductionReference pr = null;
        try {
            pr = parse(quq, Sort.of("KDefinition"), def, kem);
        } catch (ParseFailedException e) {
            System.err.println(e.getMessage() + " Line: " + e.getKException().getLocation().lineStart + " Column: " + e.getKException().getLocation().columnStart);
            assert false;
        }
        //System.out.println(pr);

        //Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1.entryState) && nc.isNullable(nt1.exitState));
        //Assert.assertEquals("Expected Nullable NTs", true, nc.isNullable(nt1));
    }

    public static ProductionReference parse(String program, Sort startSymbol, Definition definition, KExceptionManager kem) throws ParseFailedException {
        Context context = new Context();
        context.kompileOptions = new KompileOptions();
        context.globalOptions = new GlobalOptions();

        new UpdateReferencesVisitor(context).visitNode(definition);
        new CollectSubsortsVisitor(context).visitNode(definition);
        new FillInModuleContext().visitNode(definition);
        context.setTokenSorts(TokenSortCollector.collectTokenSorts(definition, context));

        // collect the syntax from those modules
        CollectTerminalsVisitor ctv = new CollectTerminalsVisitor();
        // visit all modules to collect all Terminals first
        ctv.visitNode(definition);
        Set<Sort> declaredSorts = definition.getDefinitionContext().getModuleByName(definition.getMainModule()).getModuleContext().getDeclaredSorts();
        KSyntax2GrammarStatesFilter ks2gsf = new KSyntax2GrammarStatesFilter(ctv, declaredSorts, kem);
        ks2gsf.visitNode(definition);
        Grammar grammar = ks2gsf.getGrammar();

        new CollectPrioritiesVisitor(context).visitNode(definition);

        ASTNode out = ProgramLoader.newParserParse(program, grammar.get(startSymbol.toString()), new GeneratedSource(KoreTest.class), context);
        return (ProductionReference) out;
    }
}
