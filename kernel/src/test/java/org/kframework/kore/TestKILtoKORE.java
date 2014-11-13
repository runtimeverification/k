package org.kframework.kore;

import static org.junit.Assert.assertEquals;
import static org.kframework.kore.Interface.*;
import static org.kframework.kore.Interface1.*;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import com.google.common.collect.Sets;
import org.apache.commons.io.FileUtils;
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
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.Sources;
import org.kframework.kil.StringSentence;
import org.kframework.kil.Syntax;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kore.outer.ProductionItem;
import org.kframework.parser.outer.Outer;

public class TestKILtoKORE {

    static class KILtoKORE {
        public org.kframework.kore.outer.Definition convert(Definition d) {
            Set<org.kframework.kore.outer.Require> requires = d.getItems()
                    .stream().filter(i -> i instanceof Require)
                    .map(i -> convert((Require) i)).collect(Collectors.toSet());

            Set<org.kframework.kore.outer.Module> modules = d.getItems()
                    .stream().filter(i -> i instanceof Module)
                    .map(i -> convert((Module) i)).collect(Collectors.toSet());

            return new org.kframework.kore.outer.Definition(immutable(requires), immutable(modules));
        }

        private org.kframework.kore.outer.Require convert(Require i) {
            return new org.kframework.kore.outer.Require(new File(i.getValue()));
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
                return Sets.newHashSet(convert((Import) i));
            } else if (i instanceof Syntax) {
                return convert((Syntax) i);
            } else if (i instanceof StringSentence) {
                // need a bubble here
                throw new RuntimeException("Not implemented");
            } else if (i instanceof LiterateModuleComment) {
                return Sets.newHashSet(new org.kframework.kore.outer.ModuleComment(
                        ((LiterateModuleComment) i).getValue(), convert(i.getAttributes())));
            } else if (i instanceof Sentence) {
                // I think this should have left as a bubble...
                throw new RuntimeException("Found a sentence while translating KIL");
            } else if (i instanceof PriorityExtended) {
                throw new RuntimeException("Not implemented");
            } else if (i instanceof PriorityExtendedAssoc) {
                throw new RuntimeException("Not implemented");
            } else if (i instanceof Restrictions) {
                throw new RuntimeException("Not implemented");
            } else {
                throw new RuntimeException("Unhandled case");
            }
        }

        private org.kframework.kore.outer.Sentence convert(Import s) {
            return new org.kframework.kore.outer.Import(s.getName(), convert(s.getAttributes()));
        }

        private Set<org.kframework.kore.outer.Sentence> convert(Syntax s) {
            Set<org.kframework.kore.outer.Sentence> res = new HashSet<>();
            if (s.getPriorityBlocks().size() == 0) {
                res.add(new org.kframework.kore.outer.SyntaxSort(convert(s.getDeclaredSort().getSort()),
                        convert(s.getAttributes())));
                return res;
            }

            org.kframework.kore.Sort sort =
                    convert(s.getDeclaredSort().getSort());

            for (PriorityBlock b : s.getPriorityBlocks()) {
                for (Production p : b.getProductions()) {
                    // Handle a special case first: List productions have only one item.
                    if (p.getItems().size() == 1
                            && p.getItems().get(0) instanceof UserList) {
                        UserList userList = (UserList) p.getItems().get(0);
                        org.kframework.kore.Sort elementSort = convert(userList.getSort());
                        org.kframework.kore.outer.Terminal sepTerminal =
                                new org.kframework.kore.outer.Terminal(userList.getSeparator());
                        org.kframework.kore.outer.NonTerminal elem =
                                new org.kframework.kore.outer.NonTerminal(elementSort);

                        // TODO: attributes are probably wrong

                        // lst ::= lst sep lst
                        List<org.kframework.kore.outer.ProductionItem> prod1Items =
                                new ArrayList<>();
                        prod1Items.add(new org.kframework.kore.outer.NonTerminal(sort));
                        prod1Items.add(sepTerminal);
                        prod1Items.add(new org.kframework.kore.outer.NonTerminal(sort));
                        org.kframework.kore.outer.SyntaxProduction prod1 =
                                new org.kframework.kore.outer.SyntaxProduction(
                                        sort, Seq(prod1Items), convert(p.getAttributes()));

                        // lst ::= elem
                        org.kframework.kore.outer.SyntaxProduction prod2 =
                                new org.kframework.kore.outer.SyntaxProduction(
                                        sort, Seq(elem), convert(p.getAttributes()));

                        // lst ::= .UserList
                        List<org.kframework.kore.outer.ProductionItem> prod3Items =
                                new ArrayList<>();
                        prod3Items.add(new org.kframework.kore.outer.Terminal("." + sort.toString()));
                        org.kframework.kore.outer.SyntaxProduction prod3 =
                                new org.kframework.kore.outer.SyntaxProduction(
                                        sort, Seq(prod3Items), convert(p.getAttributes()));

                        res.add(prod1);
                        res.add(prod2);
                        res.add(prod3);

                        return res;
                    }

                    List<ProductionItem> items = new ArrayList<>();
                    // TODO: when to use RegexTerminal?
                    for (org.kframework.kil.ProductionItem it : p.getItems()) {
                        if (it instanceof NonTerminal) {
                            items.add(new org.kframework.kore.outer.NonTerminal(
                                    convert(((NonTerminal) it).getSort())));
                        } else if (it instanceof UserList) {
                            throw new RuntimeException("Lists should have converted before.");
                        } else if (it instanceof Lexical) {
                            // TODO: not sure what to do
                        } else if (it instanceof Terminal) {
                            items.add(new org.kframework.kore.outer.Terminal(
                                    ((Terminal) it).getTerminal()));
                        } else {
                            throw new RuntimeException("Unhandled case");
                        }
                    }

                    org.kframework.kore.outer.SyntaxProduction prod =
                            new org.kframework.kore.outer.SyntaxProduction(
                                    sort,
                                    immutable(items),
                                    convert(p.getAttributes()));

                    res.add(prod);
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

//    @Test
//    public void syntaxWithRhs() throws IOException {
//        standardTest();
//    }

    @Test
    public void userList() throws IOException {
        standardTest();
    }

    private void standardTest() throws IOException {
        File inputFile = new File(ROOT + name.getMethodName() + ".k");
        File outputFile = new File(ROOT + name.getMethodName() + "-expected.k");

        String definitionText = FileUtils.readFileToString(inputFile);
        org.kframework.kore.outer.Definition koreDefintion = toKORE(definitionText);

        if (outputFile.isFile()) {
            String expectedOutput = FileUtils.readFileToString(outputFile);
            assertEquals(expectedOutput.trim(), koreDefintion.toString().trim());
        } else {
            assertEquals(definitionText.trim(), koreDefintion.toString().trim());
        }
    }

    private org.kframework.kore.outer.Definition toKORE(String testedDefintion) {
        Definition def = new Definition();
        def.setItems(Outer.parse(Sources.generatedBy(TestKILtoKORE.class),
                testedDefintion, null));

        System.out.println(def);

        KILtoKORE convertor = new KILtoKORE();
        org.kframework.kore.outer.Definition converted = convertor.convert(def);
        return converted;
    }
}
