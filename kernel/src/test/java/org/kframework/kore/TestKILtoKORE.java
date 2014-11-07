package org.kframework.kore;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import org.junit.Test;
import org.kframework.kil.Attributes;
import org.kframework.kil.Definition;
import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Require;
import org.kframework.kil.Sort;
import org.kframework.kil.Sources;
import org.kframework.kil.Syntax;
import org.kframework.kore.outer.Sentence;
import org.kframework.kore.outer.SyntaxSort;
import org.kframework.parser.outer.Outer;
import org.kframework.parser.utils.KoreIT;

import static org.kframework.kore.Interface1.*;

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
            Set<Sentence> items = i.getItems().stream().map(j -> convert(j))
                    .collect(Collectors.toSet());
            return new org.kframework.kore.outer.Module(i.getName(),
                    immutable(items), convert(i.getAttributes()));
        }

        private org.kframework.kore.outer.Sentence convert(ModuleItem i) {
            if (i instanceof Import) {
                convert((Import) i);
            } else if (i instanceof Syntax) {
                convert((Syntax) i);
            }
            return null;
        }

        private org.kframework.kore.outer.Sentence convert(Import s) {
            return null;
        }

        private Set<org.kframework.kore.outer.Sentence> convert(Syntax s) {
            HashSet<Sentence> res = new HashSet<org.kframework.kore.outer.Sentence>();

            if (s.getPriorityBlocks().size() == 0)
                res.add(new SyntaxSort(convert(s.getAllSorts().get(0)), null));

            for (PriorityBlock b : s.getPriorityBlocks()) {

            }

            return null;
        }

        private org.kframework.kore.Sort convert(Sort sort) {
            // TODO Auto-generated method stub
            return null;
        }

        private org.kframework.kore.Attributes convert(Attributes attributes) {
            return null;
        }
    }

    @Test
    public void basicTest() {
        Definition def = new Definition();
        String testedDefintion = requireBla + "\n" + makeModule(fooSyntax);

        def.setItems(Outer.parse(Sources.generatedBy(KoreIT.class),
                testedDefintion, null));

        KILtoKORE convertor = new KILtoKORE();
        org.kframework.kore.outer.Definition converted = convertor.convert(def);

        System.out.println(converted);
    }

    String requireBla = "require \"bla\"";
    String fooSyntax = "syntax Foo ::= \"foo\"";

    private String makeModule(String... contents) {
        String concatenated = "";
        for (String s : contents)
            concatenated += s;
        return "module EMPTY\n" + concatenated + "\nendmodule";
    }
}
