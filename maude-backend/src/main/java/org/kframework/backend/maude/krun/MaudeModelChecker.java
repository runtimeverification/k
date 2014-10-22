// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.maude.krun;

import java.util.ArrayList;
import java.util.List;

import org.kframework.backend.maude.MaudeFilter;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.KRunExecutionException;
import org.kframework.krun.XmlUtil;
import org.kframework.krun.api.KRunGraph;
import org.kframework.krun.api.KRunProofResult;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.Transition;
import org.kframework.krun.tools.LtlModelChecker;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import com.google.inject.Inject;

public class MaudeModelChecker implements LtlModelChecker {

    private final KompileOptions kompileOptions;
    private final MaudeExecutor executor;
    private final KExceptionManager kem;
    private final FileUtil files;
    private final Context context;

    @Inject
    MaudeModelChecker(
            Context context,
            KompileOptions kompileOptions,
            MaudeExecutor executor,
            KExceptionManager kem,
            FileUtil files) {
        this.context = context;
        this.kompileOptions = kompileOptions;
        this.executor = executor;
        this.kem = kem;
        this.files = files;
    }

    @Override
    public KRunProofResult<KRunGraph> modelCheck(Term formula, Term cfg) throws KRunExecutionException {
        MaudeFilter formulaFilter = new MaudeFilter(context);
        formulaFilter.visitNode(formula);
        MaudeFilter cfgFilter = new MaudeFilter(context);
        cfgFilter.visitNode(cfg);

        StringBuilder cmd = new StringBuilder()
            .append("mod MCK is\n")
            .append(" including ")
            .append(kompileOptions.mainModule()).append(" .\n\n")
            .append(" op #initConfig : -> Bag .\n\n")
            .append(" eq #initConfig  =\n")
            .append(cfgFilter.getResult()).append(" .\n")
            .append("endm\n\n")
            .append("red\n")
            .append("_`(_`)(('modelCheck`(_`,_`)).KLabel,_`,`,_(_`(_`)(Bag2KLabel(#initConfig),.KList),\n")
            .append(formulaFilter.getResult()).append(")\n")
            .append(") .");
        executor.executeKRun(cmd);
        KRunProofResult<KRunGraph> result = parseModelCheckResult();
        result.setRawOutput(files.loadFromTemp(MaudeExecutor.outFile));
        return result;
    }

    private KRunProofResult<KRunGraph> parseModelCheckResult() {
        Document doc = XmlUtil.readXMLFromFile(files.resolveTemp(MaudeExecutor.xmlOutFile).getAbsolutePath());
        NodeList list;
        Node nod;
        list = doc.getElementsByTagName("result");
        executor.assertXML(list.getLength() == 1);
        nod = list.item(0);
        executor.assertXML(nod != null && nod.getNodeType() == Node.ELEMENT_NODE);
        Element elem = (Element) nod;
        List<Element> child = XmlUtil.getChildElements(elem);
        executor.assertXML(child.size() == 1);
        String sort = child.get(0).getAttribute("sort");
        String op = child.get(0).getAttribute("op");
        executor.assertXML(op.equals("_`(_`)") && sort.equals(Sort.KITEM.toString()));
        child = XmlUtil.getChildElements(child.get(0));
        executor.assertXML(child.size() == 2);
        sort = child.get(0).getAttribute("sort");
        op = child.get(0).getAttribute("op");
        executor.assertXML(op.equals("#_") && sort.equals(Sort.KLABEL.toString()));
        sort = child.get(1).getAttribute("sort");
        op = child.get(1).getAttribute("op");
        executor.assertXML(op.equals(".KList") && sort.equals(Sort.KLIST.toString()));
        child = XmlUtil.getChildElements(child.get(0));
        executor.assertXML(child.size() == 1);
        elem = child.get(0);
        if (elem.getAttribute("op").equals("true") && elem.getAttribute("sort").equals("#Bool")) {
            return new KRunProofResult<KRunGraph>(true, null);
        } else {
            sort = elem.getAttribute("sort");
            op = elem.getAttribute("op");
            executor.assertXML(op.equals("LTLcounterexample") && sort.equals("#ModelCheckResult"));
            child = XmlUtil.getChildElements(elem);
            executor.assertXML(child.size() == 2);
            List<MaudeTransition> initialPath = new ArrayList<MaudeTransition>();
            List<MaudeTransition> loop = new ArrayList<MaudeTransition>();
            parseCounterexample(child.get(0), initialPath, context);
            parseCounterexample(child.get(1), loop, context);
            KRunGraph graph = new KRunGraph();
            Transition edge = null;
            KRunState vertex = null;
            for (MaudeTransition trans : initialPath) {
                graph.addVertex(trans.state);
                if (edge != null) {
                    graph.addEdge(edge, vertex, trans.state);
                }
                edge = trans.label;
                vertex = trans.state;
            }
            for (MaudeTransition trans : loop) {
                graph.addVertex(trans.state);
                if (edge != null) {
                    graph.addEdge(edge, vertex, trans.state);
                }
                edge = trans.label;
                vertex = trans.state;
            }
            graph.addEdge(edge, vertex, loop.get(0).state);

            return new KRunProofResult<KRunGraph>(false, graph);
        }
    }

    private static class MaudeTransition {
        public KRunState state;
        public Transition label;

        public MaudeTransition(KRunState state, Transition label) {
            this.state = state;
            this.label = label;
        }
    }

    private void parseCounterexample(Element elem, List<MaudeTransition> list, Context context) {
        String sort = elem.getAttribute("sort");
        String op = elem.getAttribute("op");
        List<Element> child = XmlUtil.getChildElements(elem);
        if (sort.equals("#TransitionList") && op.equals("_LTL_")) {
            executor.assertXML(child.size() >= 2);
            for (Element e : child) {
                parseCounterexample(e, list, context);
            }
        } else if (sort.equals("#Transition") && op.equals("LTL`{_`,_`}")) {
            executor.assertXML(child.size() == 2);
            Term t = MaudeExecutor.parseXML(child.get(0), context);

            List<Element> child2 = XmlUtil.getChildElements(child.get(1));
            sort = child.get(1).getAttribute("sort");
            op = child.get(1).getAttribute("op");
            //#Sort means we included the meta level and so it thinks Qids
            //aren' Qids even though they really are.
            executor.assertXML(child2.size() == 0 && (sort.equals("#Qid") || sort.equals("#RuleName") || sort.equals("#Sort")));
            String label = op;
            Transition trans;
            if (sort.equals("#RuleName") && op.equals("UnlabeledLtl")) {
                trans = Transition.unlabelled();
            } else if (sort.equals("#RuleName") && op.equals("deadlockLtl")) {
                trans = Transition.deadlock();
            } else {
                trans = Transition.label(label);
            }
            list.add(new MaudeTransition(new KRunState(t), trans));
        } else if (sort.equals("#TransitionList") && op.equals("LTLnil")) {
            executor.assertXML(child.size() == 0);
        } else {
            kem.registerCriticalError("Cannot parse result xml from maude due to production " + op + " of sort " + sort + ". Please file an error on the issue tracker which includes this error message.");
            executor.assertXML(false);
        }
    }


}
