package org.kframework.kore.convertors;

import org.junit.Test;
import org.kframework.definition.Module;
import org.kframework.tiny.Constructors;
import org.kframework.tiny.FreeTheory;
import org.kframework.tiny.K;
import org.kframework.tiny.KApp;
import org.kframework.tiny.Rewriter;
import org.kframework.tiny.Rule;
import org.kframework.tiny.package$;
import scala.collection.immutable.Set;

import static org.kframework.Collections.*;

import java.io.IOException;


public class TstTinyOnKORE extends BaseTest {
    @Test
    public void kore_imp() throws IOException {
        sdfTest();
    }

    protected String convert(DefinitionWithContext defWithContext) {
        KILtoKORE kilToKore = new KILtoKORE(defWithContext.context);
        Module module = kilToKore.apply(defWithContext.definition).getModule("TEST").get();
        Constructors cons = new Constructors(module);
        package$ tiny = package$.MODULE$;

        KApp program = cons.KApply(cons.KLabel("'<top>"),
                cons.KApply(cons.KLabel("'<k>"),
                        cons.KApply(cons.KLabel("'_/_"), cons.stringToId("x"), cons.stringToId("y"))),
                cons.KApply(cons.KLabel("'<state>"), cons.intToToken(1), cons.intToToken(2))
        );

        System.out.println("module = " + module);

        Rewriter rewriter = new Rewriter(module);

        Set<K> results = rewriter.rewrite(program);

        return results.mkString("\n\n");
    }

    @Override
    protected String expectedFilePostfix() {
        return "-tiny-expected.txt";
    }
}
