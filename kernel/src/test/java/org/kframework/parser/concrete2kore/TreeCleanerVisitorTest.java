package org.kframework.parser.concrete2kore;

import org.junit.Test;
import org.kframework.kore.outer.SyntaxProduction;
import org.kframework.parser.*;

import java.util.Optional;

import static org.kframework.kore.outer.Constructors.*;
import static org.kframework.kore.Constructors.*;
import static org.kframework.Collections.*;

import static org.junit.Assert.*;

public class TreeCleanerVisitorTest {

    @Test
    public void testApply() throws Exception {
//        amb([amb([NOKLABEL(amb([#emptyKRequireList()]),amb([#KModuleList(amb([#KModule(amb([#token(KModuleName,"FOO ")]),amb([#emptyKImportList()]),amb([#emptyKSentenceList()]))]),amb([#emptyKModuleList()]))]))])])

        TreeCleanerVisitor treeCleanerVisitor = new TreeCleanerVisitor();

        SyntaxProduction fooProduction = SyntaxProduction(Sort("Foo"), Seq());

        treeCleanerVisitor.apply(Constant.apply("foo", fooProduction, Optional.empty()));
    }

    @Test
    public void testMerge() throws Exception {

    }
}