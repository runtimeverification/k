package org.kframework.parser.basic;

import java.util.List;

import junit.framework.Assert;

import org.junit.Test;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Lexical;
import org.kframework.kil.Module;
import org.kframework.kil.Syntax;

public class BasicParsingTests {
    
    @Test
    public void testLexicalRules() throws Exception {
        // TODO: remove once the new parser is fully functional
        String def = "module TEST syntax Str ::= Token{((~[\\'\\n\\r\\\\])|([\\\\]~[\\n\\r]))*} endmodule";

        List<DefinitionItem> defItemList = Basic.parse("UnitTest", def, null);

        Module mod = (Module) defItemList.get(0);
        Syntax syn = (Syntax) mod.getItems().get(0);
        Lexical lex = (Lexical) syn.getPriorityBlocks().get(0).getProductions().get(0).getItems().get(0);

        Assert.assertEquals("((~[\\'\\n\\r\\\\])|([\\\\]~[\\n\\r]))*", lex.getLexicalRule());
    }
}
