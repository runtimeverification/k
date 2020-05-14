// Copyright (c) 2015-2020 K Team. All Rights Reserved.
package org.kframework.parser.outer;

import org.junit.Assert;
import org.junit.Test;
import org.kframework.parser.markdown.ASTExpressionStart;
import org.kframework.parser.markdown.TagSelector;

public class MDsourceTest {
    @Test
    public void test1() {
        String selectExp = "k";
        ASTExpressionStart mdSelectorAST = TagSelector.parseSelectorExp(selectExp);
        String mdTxt = "1\n" +
                " ```k\n" +
                " // ignore indentation\n" +
                "require \"a.md\"\n" +
                " ```\n" +
                "5\n" +
                "```{a b}\n" +
                "7\n" +
                "```\n" +
                "9\n" +
                "```{k x}\n" +
                "module TEST\n" +
                "```\n" +
                "\n" +
                "``` { k not used\n" +
                "}\n" +
                "```\n" +
                "\n" +
                "```{y k}\n" +
                "endmodule";
        String kTxt = ExtractFencedKCodeFromMarkdown.extract(mdTxt, mdSelectorAST);
        String expectedK = "\n" +
                " \n" +
                " // ignore indentation\n" +
                "require \"a.md\"\n" +
                " \n" +
                "\n" +
                " \n" +
                "\n" +
                "\n" +
                "\n" +
                " \n" +
                "module TEST\n" +
                "\n" +
                "\n" +
                "    \n" +
                "\n" +
                "\n" +
                "\n" +
                " \n" +
                "endmodule";
        Assert.assertEquals(expectedK, kTxt);
    }
}
