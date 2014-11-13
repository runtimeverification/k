package org.kframework.kore;

import static org.junit.Assert.assertEquals;
import static org.kframework.kore.Interface.*;
import static org.kframework.kore.Interface1.*;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TestName;
import org.kframework.kil.Attributes;
import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.Lexical;
import org.kframework.kil.LiterateModuleComment;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.PriorityExtended;
import org.kframework.kil.PriorityExtendedAssoc;
import org.kframework.kil.Production;
import org.kframework.kil.Require;
import org.kframework.kil.Restrictions;
import org.kframework.kil.Sort;
import org.kframework.kil.Sources;
import org.kframework.kil.StringSentence;
import org.kframework.kil.Syntax;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kore.outer.ProductionItem;
import org.kframework.parser.outer.Outer;
import org.kframework.parser.utils.KoreIT;

public class TestKILtoKORE {

    static class KILtoKORE {
        public org.kframework.kore.outer.Definition convert(Definition d) {
            Set<org.kframework.kore.outer.Require> requires = d.getItems()
                    .stream().filter(i -> i instanceof Require)
                    .map(i -> convert((Require) i)).collect(Collectors.toSet());

            Set<org.kframework.kore.outer.Module> modules = d.getItems()
                    .stream().filter(i -> i instanceof Module)
                    .map(i -> convert((Module) i)).collect(Collectors.toSet());

            return new org.kframework.kore.outer.Definition(
                    immutable(requires), immutable(modules));
        }

        private org.kframework.kore.outer.Require convert(Require i) {
            return new org.kframework.kore.outer.Require(new java.io.File(
                    i.getValue()));
        }

        private org.kframework.kore.outer.Module convert(Module i) {
            Set<org.kframework.kore.outer.Sentence> items = i.getItems().stream()
                    .flatMap(j -> convert(j).stream())
                    .collect(Collectors.toSet());
            return new org.kframework.kore.outer.Module(i.getName(),
                    immutable(items), convert(i.getAttributes()));
        }

        private Set<org.kframework.kore.outer.Sentence> convert(ModuleItem i) {
            if (i instanceof Import) {
                Set<org.kframework.kore.outer.Sentence> res = new HashSet<>();
                res.add(new org.kframework.kore.outer.Import(((Import) i)
                        .getName(), Attributes()));
                return res;
            } else if (i instanceof Syntax) {
                return convert((Syntax) i);
            } else if (i instanceof StringSentence) {
                // need a bubble here
                throw new RuntimeException("Not implemented");
            } else if (i instanceof LiterateModuleComment) {
                Set<org.kframework.kore.outer.Sentence> res = new HashSet<>();
                res.add(new org.kframework.kore.outer.ModuleComment(
                        ((LiterateModuleComment) i).getValue(), convert(i.getAttributes())));
                return res;
            } else if (i instanceof org.kframework.kil.Sentence) {
                // I think this should have left as a bubble...
                throw new RuntimeException("Found a sentence while translating KIL");
            } else if (i instanceof PriorityExtended) {
                throw new RuntimeException("Not implemented");
            } else if (i instanceof PriorityExtendedAssoc) {
                throw new RuntimeException("Not implemented");
            } else if (i instanceof Restrictions) {
                throw new RuntimeException("Not implemented");
            } else {
                throw new RuntimeException("Not implemented");
            }
        }

        private org.kframework.kore.outer.Sentence convert(Import s) {
            return new org.kframework.kore.outer.Import(s.getName(), convert(s.getAttributes()));
        }

        private Set<org.kframework.kore.outer.Sentence> convert(Syntax s) {
            Set<org.kframework.kore.outer.Sentence> res = new HashSet<>();
            res.add(new org.kframework.kore.outer.SyntaxSort(convert(s.getDeclaredSort().getSort()),
                    convert(s.getAttributes())));

            for (PriorityBlock b : s.getPriorityBlocks()) {
                // ignoring priorities for now
                for (Production p : b.getProductions()) {
                    List<ProductionItem> items = new ArrayList<>();
                    // TODO: when to use RegexTerminal?
                    for (org.kframework.kil.ProductionItem it : p.getItems()) {
                        if (it instanceof NonTerminal) {
                            items.add(new org.kframework.kore.outer.NonTerminal(
                                    convert(((NonTerminal) it).getSort())));
                        } else if (it instanceof UserList) {
                            // TODO: not sure what to do
                        } else if (it instanceof Lexical) {
                            // TODO: not sure what to do
                        } else if (it instanceof Terminal) {
                            items.add(new org.kframework.kore.outer.Terminal(
                                    ((Terminal) it).getTerminal()));
                        }
                    }

                    org.kframework.kore.outer.SyntaxProduction prod =
                            new org.kframework.kore.outer.SyntaxProduction(
                                    convert(s.getDeclaredSort().getSort()),
                                    null, // TODO: convert `items` to seq
                                    convert(p.getAttributes()));
                }
            }

            return res;
        }

        private org.kframework.kore.Sort convert(Sort sort) {
            return Sort(sort.getName());
        }

        private org.kframework.kore.Attributes convert(Attributes attributes) {
            Set<K> attributesSet = attributes
                    .keySet()
                    .stream()
                    .map(key -> {
                        String keyString = key.toString();
                        String valueString = attributes.get(key).getValue()
                                .toString();

                        return (K) KApply(
                                KLabel(keyString),
                                KList(KToken(Sort("AttributeValue"),
                                        KString(valueString))));
                    }).collect(Collectors.toSet());

            return Attributes(KList(attributesSet));
        }
    }

    private static final String ROOT = "src/test/resources/convertor-tests/";

    @Rule
    public TestName name = new TestName();

    @Test
    public void emptyModule() throws IOException {
        standardTest();
    }

    @Test
    public void simpleSyntax() throws IOException {
        standardTest();
    }

    @Test
    public void syntaxWithAttributes() throws IOException {
        standardTest();
    }

    private void standardTest() throws IOException {
        File file = new File(ROOT + name.getMethodName() + ".k");
        String definitionText = Files.lines(file.toPath())
                .reduce((x, y) -> x + "\n" + y).get();

        org.kframework.kore.outer.Definition koreDefintion = toKORE(definitionText);
        assertEquals(definitionText.trim(), koreDefintion.toString().trim());
    }

    private org.kframework.kore.outer.Definition toKORE(String testedDefintion) {
        Definition def = new Definition();
        def.setItems(Outer.parse(Sources.generatedBy(KoreIT.class),
                testedDefintion, null));
        
        System.out.println(def);

        KILtoKORE convertor = new KILtoKORE();
        org.kframework.kore.outer.Definition converted = convertor.convert(def);
        return converted;
    }
}
