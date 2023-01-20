package org.kframework.lsp;

import org.eclipse.lsp4j.Position;
import org.junit.Test;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class LSPTests {

    @Test
    public void test1() {
        String def = "" +
                "module TEST \n" +
                "syntax Exps ::= Exp \",\" Exps [klabel('Exps)] \n" +
                "| Exp \n" +
                "syntax Exp ::= Id \n" +
                "syntax Stmt ::= \"val\" Exps \";\" Stmt [klabel('Decl)] \n" +
                "syntax {Sort} Sort ::= \"(\" Sort \")\" [bracket] \n" +
                "syntax KItem ::= (Id, Stmt) [klabel('tuple)] \n" +
                "syntax Id \n" +
                "syntax K \n" +
                "endmodule\n";
        KTextDocument doc = new KTextDocument();
        doc.updateText(def);
        System.out.println(doc.getContextAt(new Position(1, 1)));
    }

    @Test
    public void test2() {
        Pattern p = Pattern.compile("(aa)");
        String content = "aa bb aa dd";
        Matcher m = p.matcher(content);
        String context = "aa";
        while (m.find()) {
            context = m.group();
            System.out.println(m.start() + " - " + m.end());
            //if (lines[m.regionEnd()] > pos.getLine() || lines[m.regionEnd()] == pos.getLine() && columns[m.regionEnd()] > pos.getCharacter())
            //    break;
        }

    }
}