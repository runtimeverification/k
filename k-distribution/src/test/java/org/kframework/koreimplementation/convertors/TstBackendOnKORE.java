package org.kframework.koreimplementation.convertors;

import org.junit.Test;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.indexing.IndexingTable;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.symbolic.SymbolicRewriter;
import org.kframework.definition.Module;
import org.kframework.kompile.KompileOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import scala.Option;

import java.io.IOException;

public class TstBackendOnKORE extends BaseTest {
    @Test
    public void kore_imp() throws IOException {
        sdfTest();
    }

    protected String convert(BaseTest.DefinitionWithContext defWithContext) {
        KILtoKORE kilToKore = new KILtoKORE(defWithContext.context);
        Module module = kilToKore.apply(defWithContext.definition).getModule("TEST").get();

        Definition definition = new Definition(module);
        TermContext termContext = TermContext.of(new GlobalContext(
                null,
                null,
                null,
                new KItem.KItemOperations(Tool.KRUN, new JavaExecutionOptions(), null, null, new GlobalOptions()),
                null));
        termContext.global().setDefinition(definition);
        definition.addKoreRules(module, termContext);
        definition.setIndex(new IndexingTable(() -> definition, new IndexingTable.Data()));
        SymbolicRewriter rewriter = new SymbolicRewriter(definition, new KompileOptions(), new JavaExecutionOptions(), null);
        return rewriter.rewrite(
                new ConstrainedTerm(
                        new KItem(
                                KLabelConstant.of("'notBool_", definition),
                                KList.singleton(BoolToken.TRUE),
                                Sort.BOOL,
                                false),
                        termContext),
                null,
                -1,
                false)
                .toString();

    }

    @Override
    protected String expectedFilePostfix() {
        return "-backend-expected.txt";
    }
}
