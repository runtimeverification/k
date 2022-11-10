// Copyright (c) 2015-2020 K Team. All Rights Reserved.
package org.kframework.parser.outer;

import org.junit.Assert;
import org.junit.Test;
import org.kframework.attributes.Source;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.markdown.TagSelector;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;

public class MDsourceTest {
    @Test
    public void test1() {
        String selectExp = "k";
        String mdTxt = "1\n" +
                " ```k\n" +
                " // ignore indentation\n" +
                "require \"a.md\"\n" +
                " ```\n" +
                "6\n" +
                "```{a b}\n" +
                "8\n" +
                "```\n" +
                "10\n" +
                "```{k x}\n" +
                "module TEST\n" +
                "```\n" +
                "\n" +
                "``` { k hidden warning\n" +
                "}\n" +
                "```\n" +
                "\n" +
                "```{y k}\n" +
                "endmodule";
        GlobalOptions go = new GlobalOptions();
        go.warnings = GlobalOptions.Warnings.ALL;
        KExceptionManager kem = new KExceptionManager(go);
        ExtractFencedKCodeFromMarkdown mdExtractor = new ExtractFencedKCodeFromMarkdown(kem, selectExp);
        String kTxt = mdExtractor.extract(mdTxt, new Source(MDsourceTest.class.toString()));
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
        Assert.assertEquals(1, kem.getExceptions().size());
    }

    @Test(expected = KEMException.class)
    public void test2() {
        String selectExp = "k|";
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        ExtractFencedKCodeFromMarkdown mdExtractor = new ExtractFencedKCodeFromMarkdown(kem, selectExp);
    }

    @Test(expected = KEMException.class)
    public void test3() {
        String selectExp = "k|a b";
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        ExtractFencedKCodeFromMarkdown mdExtractor = new ExtractFencedKCodeFromMarkdown(kem, selectExp);
    }

    @Test
    public void test4() {
        KExceptionManager kem = new KExceptionManager(new GlobalOptions(false, GlobalOptions.Warnings.ALL, false));
        TagSelector.parseTags("k a", new Source(MDsourceTest.class.toString()), kem);
        Assert.assertEquals(1, kem.getExceptions().size());
    }

    @Test
    public void test5() {
        KExceptionManager kem = new KExceptionManager(new GlobalOptions(false, GlobalOptions.Warnings.ALL, false));
        TagSelector.parseTags("{k a", new Source(MDsourceTest.class.toString()), kem);
        Assert.assertEquals(1, kem.getExceptions().size());
    }

    @Test
    public void test6() {
        KExceptionManager kem = new KExceptionManager(new GlobalOptions());
        Assert.assertEquals(2, TagSelector.parseTags("{k a}", new Source(MDsourceTest.class.toString()), kem).size());
        Assert.assertEquals(2, TagSelector.parseTags("{.k .a}", new Source(MDsourceTest.class.toString()), kem).size());
        Assert.assertEquals(2, TagSelector.parseTags("{.k a}", new Source(MDsourceTest.class.toString()), kem).size());
        Assert.assertEquals(1, TagSelector.parseTags("k", new Source(MDsourceTest.class.toString()), kem).size());
        Assert.assertEquals(0, TagSelector.parseTags("", new Source(MDsourceTest.class.toString()), kem).size());
        Assert.assertEquals(0, TagSelector.parseTags(" ", new Source(MDsourceTest.class.toString()), kem).size());
    }
}
