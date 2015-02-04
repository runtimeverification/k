// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import org.apache.commons.lang3.tuple.MutablePair;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Location;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Source;
import org.kframework.kil.StringBuiltin;
import org.kframework.krun.api.KRunGraph;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.Transition;
import org.kframework.krun.api.Transition.TransitionType;
import org.kframework.transformation.Transformation;
import org.kframework.utils.inject.Concrete;
import org.kframework.utils.inject.InjectGeneric;

import com.google.inject.Inject;

import java.util.HashMap;
import java.util.Map;

public class PrintTransition implements Transformation<Transition, String> {

    @InjectGeneric private Transformation<ASTNode, String> astNodePrinter;
    @InjectGeneric private Transformation<KRunState, String> statePrinter;
    private Definition definition;
    private Map<Pair<Source, Location>, ModuleItem> ruleStore;

    @Inject
    public PrintTransition() {
    }

    public PrintTransition(
            Transformation<ASTNode, String> astNodePrinter,
            Transformation<KRunState, String> statePrinter) {
        this.astNodePrinter = astNodePrinter;
        this.statePrinter = statePrinter;
        this.ruleStore = new HashMap<>();
    }

    /**
     * Populates a map containing the unparsed rules, for pretty printing.
     */
    private void populateRuleStore() {
        definition.getItems().stream().filter((item) -> item instanceof Module).forEach((item) -> {
            ((Module) item).getItems().stream().forEach((moduleItem) -> {
                Source src = moduleItem.getSource();
                Location location = moduleItem.getLocation();
                if (src != null && location != null) {
                    ruleStore.put(new MutablePair<>(src, location), moduleItem);
                }
            });
        });
    }

    public static final String PRINT_VERBOSE_GRAPH = "printVerboseGraph";

    @Override
    public String run(Transition trans, Attributes a) {
        StringBuilder sb = new StringBuilder();
        boolean verbose = a.typeSafeGet(Boolean.class, PRINT_VERBOSE_GRAPH);
        KRunGraph graph = a.typeSafeGet(KRunGraph.class);
        if (!(definition != null)) {
            definition = a.typeSafeGet(Attribute.Key.get(Definition.class));
            populateRuleStore();
        }
        if (trans.getType() == TransitionType.RULE) {
            if (verbose) {
                sb.append(astNodePrinter.run(trans.getRule(), a));
            } else {
                Attributes ruleAttrs = trans.getRule().getAttributes();
                sb.append("\nRule tagged ");
                sb.append(astNodePrinter.run(ruleAttrs, a));
            }
        } else if (trans.getType() == TransitionType.REDUCE) {
            sb.append("\nFunction evaluation");
        } else if (trans.getType() == TransitionType.UNLABELLED) {
            sb.append("\nUnlabelled rule");
        } else {
            sb.append("\nRead " + StringBuiltin.of(trans.getReadString()).value());
        }

        if (verbose) {
            sb.append("\n");
            sb.append(statePrinter.run(graph.getSource(trans), a));
            sb.append("\n=>\n");
            sb.append(statePrinter.run(graph.getDest(trans), a));
            sb.append("\n");
        } else {
            sb.append(" [Node ");
            sb.append(graph.getSource(trans).getStateId());
            sb.append(", Node ");
            sb.append(graph.getDest(trans).getStateId());
            sb.append("]");
        }
        return sb.toString();
    }

    @Override
    public String getName() {
        return "Print transition";
    }

}
