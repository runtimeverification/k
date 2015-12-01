// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import com.google.common.collect.Lists;
import org.junit.Before;
import org.junit.Test;
import org.kframework.attributes.Att;
import org.kframework.attributes.Source;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Labels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Sentence;
import org.kframework.definition.Terminal;
import org.kframework.kil.Attribute;
import org.kframework.kompile.Kompile;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.concrete2kore.ParserUtils;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.collection.Set;

import java.io.File;
import java.util.Arrays;
import java.util.Collections;
import java.util.Map;

import static org.junit.Assert.*;
import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.Att;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class GenerateSentencesFromConfigDeclTest {

    Definition def;

    @Before
    public void setUp() {
        String definitionText;
        FileUtil files = FileUtil.testFileUtil();
        ParserUtils parser = new ParserUtils(files, new KExceptionManager(new GlobalOptions()));
        File definitionFile = new File(Kompile.BUILTIN_DIRECTORY.toString() + "/kast.k");
        definitionText = files.loadFromWorkingDirectory(definitionFile.getPath());

        def =
                parser.loadDefinition("K", "K", definitionText,
                        definitionFile,
                        definitionFile.getParentFile(),
                        Lists.newArrayList(Kompile.BUILTIN_DIRECTORY),
                        true);
    }

    @Test
    public void testSingleTop() {
        K configuration = cell("threads", Collections.emptyMap(),
                cell("thread", Collections.singletonMap("multiplicity", "*"),
                        cells(cell("k", Collections.emptyMap(), KApply(KLabel("#SemanticCastToKItem"), KToken("$PGM", Sorts.KConfigVar()))),
                                cell("opt", Collections.singletonMap("multiplicity", "?"),
                                        KApply(KLabel(".Opt"))))));
        Module m1 = Module("CONFIG", Set(def.getModule("KSEQ").get()), Set(Production(".Opt", Sort("OptCellContent"), Seq(Terminal("")))), Att());
        RuleGrammarGenerator parserGen = new RuleGrammarGenerator(def, true);
        Module m = parserGen.getCombinedGrammar(parserGen.getConfigGrammar(m1)).getExtensionModule();
        Set<Sentence> gen = GenerateSentencesFromConfigDecl.gen(configuration, BooleanUtils.FALSE, Att(), m);
        Att initializerAtts = Att().add("initializer");
        Att productionAtts = initializerAtts.add("function");
        Set<Sentence> reference = Set(Production("<threads>", Sort("ThreadsCell"),
                        Seq(Terminal("<threads>"), NonTerminal(Sort("ThreadCellBag")), Terminal("</threads>")),
                        Att().add("cell").add("topcell")),
                SyntaxSort(Sort("ThreadCellBag"), Att().add("hook", "BAG.Bag")),
                Production("_ThreadCellBag_", Sort("ThreadCellBag"),
                        Seq(NonTerminal(Sort("ThreadCellBag")), NonTerminal(Sort("ThreadCellBag"))),
                        Att().add("assoc","").add("comm","").add("unit",".ThreadCellBag")
                                .add("element","ThreadCellBagItem").add("wrapElement","<thread>")
                                .add("function").add("hook","BAG.concat")),
                Production(".ThreadCellBag", Sort("ThreadCellBag"),
                        Seq(Terminal(".ThreadCellBag")),
                        Att().add("function").add("hook","BAG.unit")),
                Production(Sort("ThreadCellBag"),
                        Seq(NonTerminal(Sort("ThreadCell")))),
                Production("ThreadCellBagItem", Sort("ThreadCellBag"),
                        Seq(Terminal("ThreadCellBagItem"), Terminal("("), NonTerminal(Sort("ThreadCell")), Terminal(")")),
                        Att().add("function").add("hook","BAG.element")),
                Production("<thread>", Sort("ThreadCell"),
                        Seq(Terminal("<thread>"), NonTerminal(Sort("KCell")), NonTerminal(Sort("OptCell")), Terminal("</thread>")),
                        Att().add("cell").add("multiplicity","*")),
                Production("<k>", Sort("KCell"),
                        Seq(Terminal("<k>"), NonTerminal(Sort("K")), Terminal("</k>")),
                        Att().add("cell").add("maincell")),
                Production("<opt>", Sort("OptCell"),
                        Seq(Terminal("<opt>"), NonTerminal(Sort("OptCellContent")), Terminal("</opt>")),
                        Att().add("cell").add("multiplicity","?").add("unit",".OptCell")),
                Production(".OptCell", Sort("OptCell"),
                        Seq(Terminal(".OptCell"))),
                Production("initThreadsCell", Sort("ThreadsCell"),
                        Seq(Terminal("initThreadsCell"), Terminal("("), NonTerminal(Sort("Map")), Terminal(")")),
                        productionAtts),
                Production("initThreadCell", Sort("ThreadCell"),
                        Seq(Terminal("initThreadCell"), Terminal("("), NonTerminal(Sort("Map")), Terminal(")")),
                        productionAtts),
                Production("initKCell", Sort("KCell"),
                        Seq(Terminal("initKCell"), Terminal("("), NonTerminal(Sort("Map")), Terminal(")")),
                        productionAtts),
                Production("initOptCell", Sort("OptCell"),
                        Seq(Terminal("initOptCell")),
                        productionAtts),
                Rule(KRewrite(KApply(KLabel("initThreadsCell"), KVariable("Init")),
                                IncompleteCellUtils.make(KLabel("<threads>"), false,
                                        KApply(KLabel("initThreadCell"), KVariable("Init")), false)),
                        BooleanUtils.TRUE, BooleanUtils.FALSE, initializerAtts),
                Rule(KRewrite(KApply(KLabel("initThreadCell"), KVariable("Init")),
                                IncompleteCellUtils.make(KLabel("<thread>"), false,
                                        Arrays.asList(KApply(KLabel("initKCell"), KVariable("Init")),
                                                KApply(KLabel(KLabels.CELLS))), false)),
                        BooleanUtils.TRUE, BooleanUtils.TRUE, initializerAtts),
                Rule(KRewrite(KApply(KLabel("initKCell"), KVariable("Init")),
                                IncompleteCellUtils.make(KLabel("<k>"), false, KApply(KLabel("#SemanticCastToKItem"), KApply(KLabel("Map:lookup"),
                                        KVariable("Init"),
                                        KToken("$PGM", Sorts.KConfigVar()))), false)),
                        BooleanUtils.TRUE, BooleanUtils.TRUE, initializerAtts),
                Rule(KRewrite(KApply(KLabel("initOptCell")),
                                IncompleteCellUtils.make(KLabel("<opt>"), false, KApply(KLabel(".Opt")), false)),
                        BooleanUtils.TRUE, BooleanUtils.TRUE, initializerAtts),
                Production("<threads>-fragment", Sort("ThreadsCellFragment"),
                        Seq(Terminal("<threads>-fragment"),NonTerminal(Sort("ThreadCellBag")),Terminal("</threads>-fragment")),
                        Att().add(Attribute.CELL_FRAGMENT_KEY,"ThreadsCell")),
                Production("<thread>-fragment", Sort("ThreadCellFragment"),
                        Seq(Terminal("<thread>-fragment"),NonTerminal(Sort("KCellOpt")),NonTerminal(Sort("OptCellOpt")),Terminal("</thread>-fragment")),
                        Att().add(Attribute.CELL_FRAGMENT_KEY,"ThreadCell")),
                Production(Sort("OptCellOpt"), Seq(NonTerminal(Sort("OptCell")))),
                Production("noOptCell", Sort("OptCellOpt"), Seq(Terminal("noOptCell")),Att().add(Attribute.CELL_OPT_ABSENT_KEY, "OptCell")),
                Production(Sort("KCellOpt"), Seq(NonTerminal(Sort("KCell")))),
                Production("noKCell", Sort("KCellOpt"), Seq(Terminal("noKCell")),Att().add(Attribute.CELL_OPT_ABSENT_KEY, "KCell"))
            );

        assertEquals("Produced unexpected productions", Set(), gen.$amp$tilde(reference));
        assertEquals("Missing expected productions", Set(), reference.$amp$tilde(gen));
        // Production.equals ignores attributes, but they are important here
        nextgen:
        for (Sentence g : iterable(gen)) {
            for (Sentence r : iterable(reference)) {
                if (g.equals(r)) {
                    assertEquals("Production "+r+" generated with incorrect attributes", r.att(), g.att());
                    continue nextgen;
                }
            }
            assert false; // We checked set equality above
        }
    }

    private KApply cells(K cell1, K cell2) {
        return KApply(KLabel(KLabels.CELLS), cell1, cell2);
    }

    private KApply cell(String s, Map<String, String> att, K body) {
        K cellAtt = att.entrySet().stream()
                .map(e -> KApply(KLabel("#cellProperty"),
                        KToken(e.getKey(), Sort("#CellName")),
                        KToken(StringUtil.enquoteKString(e.getValue()), Sort("KString"))))
                .reduce(KApply(KLabel("#cellPropertyListTerminator")), (k1, k2) -> KApply(KLabel("#cellPropertyList"), k2, k1));
        return KApply(KLabel("#configCell"), KToken(s, Sort("#CellName")), cellAtt, body, KToken(s, Sort("#CellName")));
    }
}
