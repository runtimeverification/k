// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.lsp;


import org.eclipse.lsp4j.CompletionItem;
import org.eclipse.lsp4j.CompletionItemKind;
import org.eclipse.lsp4j.InsertTextFormat;
import org.jetbrains.annotations.NotNull;
import org.kframework.attributes.Att;
import org.kframework.kil.Module;
import org.kframework.kil.*;
import org.kframework.kore.Sort;
import scala.Tuple2;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.kframework.Collections.immutable;

/**
 * Helper methods for building CompletionItems
 */
public class CompletionHelper {

    static Pattern ptrn = Pattern.compile("[a-zA-Z0-9#]+");

    // create the list of CompletionItems for every piece of syntax
    // for now we filter by alphanumeric but can be improved greatly.
    public static List<CompletionItem> getRuleCompletion(List<DefinitionItem> dis) {
        List<CompletionItem> lci = new ArrayList<>();
        // Traverse all the modules and all the syntax declarations to find the Terminals in productions
        // For each Terminal that follows the <ptrn> above, create a CompletionItem with some documentation
        // Tree structure: Definition -> Module -> Syntax -> PriorityBlock -> Production -> Terminal
        dis.stream().filter(i -> i instanceof Module)
                .map(m -> ((Module) m))
                .forEach(m -> m.getItems().stream()
                        .filter(mi -> mi instanceof Syntax)
                        .map(s -> ((Syntax) s))
                        .forEach(s -> s.getPriorityBlocks()
                                .forEach((pb -> pb.getProductions()
                                        .forEach(p -> {
                                                    if (p.getItems().get(0) instanceof Terminal && ptrn.matcher(((Terminal)p.getItems().get(0)).getTerminal()).matches()) {
                                                        CompletionItem completionItem = buildRuleCompletionItem(m, s, p);
                                                        lci.add(completionItem);
                                                    } else
                                                        p.getItems().stream()
                                                                .filter(pi -> pi instanceof Terminal)
                                                                .map(t -> (Terminal) t)
                                                                .forEach(t -> {
                                                                    if (ptrn.matcher(t.getTerminal()).matches()) {
                                                                        CompletionItem completionItem = buildRuleCompletionItem(m, s, p, t);
                                                                        lci.add(completionItem);
                                                                    }
                                                                });
                                                }
                                        )))));

        return lci;
    }

    // for productions that start with a valid terminal
    // build a code snippet with tabstops
    @NotNull
    public static CompletionItem buildRuleCompletionItem(Module m, Syntax s, Production p) {
        CompletionItem completionItem = new CompletionItem();
        Terminal t = (Terminal) p.getItems().get(0);
        completionItem.setLabel(t.getTerminal());
        StringBuilder snip = new StringBuilder();
        int codeSnip = 1;
        for (int i = 0; i < p.getItems().size(); i++) {
            ProductionItem pi = p.getItems().get(i);
            if (pi instanceof Terminal) {
                String trm = ((Terminal) pi).getTerminal();
                if (i > 0 && !"(".equals(trm) && !")".equals(trm) && !",".equals(trm))
                    snip.append(" ");
                snip.append(((Terminal) pi).getTerminal());
                if (i < p.getItems().size() - 1 && !"(".equals(trm) && !")".equals(trm))
                    snip.append(" ");
            }
            if (pi instanceof NonTerminal) {
                snip.append("${");
                snip.append(codeSnip++);
                snip.append(":_:");
                snip.append(((NonTerminal) pi).getSort());
                snip.append("}");
            }
        }

        completionItem.setInsertText(snip.toString());
        completionItem.setDetail("module " + m.getName());
        String doc = "syntax ";
        doc += !s.getParams().isEmpty() ?
                "{" + s.getParams().stream().map(Sort::toString).collect(Collectors.joining(", ")) + "} " : "";
        doc += s.getDeclaredSort() + " ::= ";
        doc += p.toString();
        completionItem.setDocumentation(doc);
        completionItem.setInsertTextFormat(InsertTextFormat.Snippet);
        completionItem.setKind(CompletionItemKind.Function);
        return completionItem;
    }

    @NotNull
    private static CompletionItem buildRuleCompletionItem(Module m, Syntax s, Production p, Terminal t) {
        CompletionItem completionItem = new CompletionItem();
        completionItem.setLabel(t.getTerminal());
        completionItem.setInsertText(t.getTerminal());
        completionItem.setDetail("module " + m.getName());
        String doc = "syntax ";
        doc += !s.getParams().isEmpty() ?
                "{" + s.getParams().stream().map(Sort::toString).collect(Collectors.joining(", ")) + "} " : "";
        doc += s.getDeclaredSort() + " ::= ";
        doc += p.toString();
        completionItem.setDocumentation(doc);
        completionItem.setInsertTextFormat(InsertTextFormat.PlainText);
        completionItem.setKind(CompletionItemKind.Operator);
        return completionItem;
    }

    public static CompletionItem getNewRequiresCompletion() {
        CompletionItem completionItem = new CompletionItem();
        completionItem.setLabel("requires");
        completionItem.setInsertText("requires \"${1:file}\"");
        completionItem.setInsertTextFormat(InsertTextFormat.Snippet);
        completionItem.setKind(CompletionItemKind.Keyword);
        return completionItem;
    }

    public static CompletionItem getNewModuleCompletion() {
        CompletionItem completionItem = new CompletionItem();
        completionItem.setLabel("module");
        completionItem.setInsertText("module ${0:NAME}\nendmodule");
        completionItem.setInsertTextFormat(InsertTextFormat.Snippet);
        completionItem.setKind(CompletionItemKind.Keyword);
        return completionItem;
    }

    public static List<CompletionItem> getNewSentenceCompletion() {
        CompletionItem completionItem = new CompletionItem();
        completionItem.setLabel("syntax");
        completionItem.setInsertText("syntax ${1:SORT} ::= $0");
        completionItem.setInsertTextFormat(InsertTextFormat.Snippet);
        completionItem.setKind(CompletionItemKind.Keyword);

        return List.of(completionItem,
                new CompletionItem("rule"),
                new CompletionItem("configuration"),
                new CompletionItem("context"),
                new CompletionItem("claim"));
    }

    public static CompletionItem getNewImportCompletion() {
        CompletionItem completionItem = new CompletionItem();
        completionItem.setLabel("imports");
        completionItem.setInsertText("imports ${0:NAME}");
        completionItem.setInsertTextFormat(InsertTextFormat.Snippet);
        completionItem.setKind(CompletionItemKind.Keyword);
        return completionItem;
    }

    public static List<CompletionItem> getImportCompletion(List<DefinitionItem> allDi) {
        return allDi.stream()
                .filter(mi2 -> mi2 instanceof Module)
                .map(m2 -> ((Module) m2))
                .map(m2 -> {
                    CompletionItem ci = new CompletionItem();
                    ci.setLabel(m2.getName());
                    ci.setInsertText(m2.getName());
                    ci.setDetail(Path.of(m2.getSource().source()).getFileName().toString());
                    ci.setKind(CompletionItemKind.Module);
                    return ci;
                }).collect(Collectors.toList());
    }

    // create a list of all the visible declared sorts
    public static List<CompletionItem> getSyntaxCompletion(List<DefinitionItem> allDi) {
        Map<String, Set<Att>> allSorts = allDi.stream().filter(i -> i instanceof Module)
                .map(m3 -> ((Module) m3))
                .flatMap(m3 -> m3.getItems().stream()
                        .filter(mi3 -> mi3 instanceof Syntax)
                        .map(s -> ((Syntax) s))
                        .filter(s -> !s.getParams().contains(s.getDeclaredSort().getRealSort()))
                        .map(s -> Tuple2.apply(s.getDeclaredSort().getRealSort().name(), s.getAttributes())))
                .collect(Collectors.groupingBy(Tuple2::_1, Collectors.mapping(Tuple2::_2, Collectors.toSet())));
        Map<String, Att> allSorts2 = allSorts.entrySet().stream()
                .map(e -> Tuple2.apply(e.getKey(), Att.mergeAttributes(immutable(e.getValue()))))
                .collect(Collectors.toMap(Tuple2::_1, Tuple2::_2));
        return allSorts2.entrySet().stream().map(e -> {
            CompletionItem ci = new CompletionItem();
            ci.setLabel(e.getKey());
            ci.setInsertText(e.getKey());
            // TODO: to calculate properly we need to recurse through the inclusion tree
            // and find the first module to declare the sort. This should be easy to get
            // when we connect to the kompile pipeline.
            //ci.setDetail("module " + m.getName());
            String documentation = "syntax " + e.getKey() + " ";
            documentation += e.getValue().toString();
            ci.setDocumentation(documentation);
            ci.setKind(CompletionItemKind.TypeParameter);
            return ci;
        }).collect(Collectors.toList());
    }
}
