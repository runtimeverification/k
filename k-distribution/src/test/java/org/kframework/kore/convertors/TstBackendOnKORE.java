// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import org.junit.Test;

import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.indexing.IndexingTable;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.backend.java.symbolic.Equality;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.symbolic.JavaSymbolicCommonModule;
import org.kframework.backend.java.symbolic.SymbolicRewriter;
import org.kframework.backend.java.util.JavaKRunState;
import org.kframework.definition.Module;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.api.KRunState;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;

import java.io.IOException;

import scala.collection.JavaConversions;

import com.google.inject.Guice;
import com.google.inject.Injector;


public class TstBackendOnKORE extends BaseTest {
    @Test
    public void kore_imp() throws IOException {
        sdfTest();
    }

    protected String convert(BaseTest.DefinitionWithContext defWithContext) {
        KILtoKORE kilToKore = new KILtoKORE(defWithContext.context);
        Module module = kilToKore.apply(defWithContext.definition).getModule("TEST").get();

        Definition definition = new Definition(module, null);

        Injector injector = Guice.createInjector(new JavaSymbolicCommonModule() {
            @Override
            protected void configure() {
                super.configure();
                bind(GlobalOptions.class).toInstance(new GlobalOptions());
                bind(Definition.class).toInstance(definition);
                bind(Tool.class).toInstance(Tool.KRUN);
            }
        });
        TermContext termContext = TermContext.of(new GlobalContext(
                null,
                new Equality.EqualityOperations(() -> definition, new JavaExecutionOptions()),
                null,
                new KItem.KItemOperations(Tool.KRUN, new JavaExecutionOptions(), null, () -> injector.getInstance(BuiltinFunction.class), new GlobalOptions()),
                Tool.KRUN));
        termContext.global().setDefinition(definition);

        JavaConversions.setAsJavaSet(module.attributesFor().keySet()).stream()
                .map(l -> KLabelConstant.of(l.name(), definition))
                .forEach(definition::addKLabel);
        definition.addKoreRules(module, termContext);

        definition.setIndex(new IndexingTable(() -> definition, new IndexingTable.Data()));

        SymbolicRewriter rewriter = new SymbolicRewriter(definition, new KompileOptions(), new JavaExecutionOptions(), new KRunState.Counter());
        KSequence.Builder builder1 = KSequence.builder();
        builder1.concatenate(new KItem(
                KLabelConstant.of("'_/_", definition),
                KList.concatenate(
                        UninterpretedToken.of(Sort.of("Id"), "x1"),
                        UninterpretedToken.of(Sort.of("Id"), "x2")),
                Sort.of("AExp"),
                true));
        Term kContent = builder1.build();
        BuiltinMap.Builder builder2 = BuiltinMap.builder(termContext);
        builder2.put(UninterpretedToken.of(Sort.of("Id"), "x1"), IntToken.of(1));
        builder2.put(UninterpretedToken.of(Sort.of("Id"), "x2"), IntToken.of(0));
        Term stateContent = builder2.build();
        return ((JavaKRunState) rewriter.rewrite(
                new ConstrainedTerm(
                        new KItem(
                                KLabelConstant.of("'<top>", definition),
                                KList.concatenate(
                                        new KItem(
                                                KLabelConstant.of("'<k>", definition),
                                                KList.concatenate(kContent),
                                                Sort.of("KCell"),
                                                true),
                                        new KItem(
                                                KLabelConstant.of("'<state>", definition),
                                                KList.concatenate(stateContent),
                                                Sort.of("StateCell"),
                                                true)),
                        Sort.of("TopCell"),
                        true),
                termContext),
                null,
                -1,
                false))
                .getJavaKilTerm().toString();
    }

    @Override
    protected String expectedFilePostfix() {
        return "-backend-expected.txt";
    }
}
