// Copyright (c) 2012-2014 K Team. All Rights Reserved.

package org.kframework.backend.symbolic;

import junit.framework.Assert;

import org.junit.Before;
import org.junit.Test;
import org.kframework.kil.Attribute;
import org.kframework.compile.sharing.FreshVariableNormalizer;
import org.kframework.kil.Attributes;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.Production;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.mockito.Mockito;

import com.google.common.collect.HashMultimap;

import java.util.Map;
import java.util.Set;

/**
 * Created on 10/04/14.
 */
public class LTLModelCheckerTest {

    Context context;
    Map<String, Set<Production>> productions;

    @Before
    public void setUp() {
        context = Mockito.mock(Context.class);
        context.klabels = HashMultimap.create();
    }

    @Test
    public void testSymbolicLTLStateRuleTransformer() {

        // create the input rule
        // LHS
        Variable inputLTLState = new Variable("B", Sort.BAG);
        KApp inputLTLStateKApp = KApp.of(new KInjectedLabel(inputLTLState), KList.EMPTY);
        Variable X = new Variable("X", Sort.ID);
        Variable I = new Variable("I", Sort.INT);
        KApp predicate = KApp.of(KLabelConstant.of("eq"), X, I);
        Term inputLhs = KApp.of(KLabelConstant.of(ResolveLtlAttributes.LTL_SAT), inputLTLStateKApp, predicate);

        // RHS
        Term inputRhs = BoolBuiltin.TRUE;

        // requires
        KApp val = KApp.of(KLabelConstant.of("val"), inputLTLStateKApp, X.shallowCopy());
        Term inputRequires = KApp.of(KLabelConstant.KEQ, val, I.shallowCopy());

        // attributes
        Attributes inputAttrs = new Attributes();
        inputAttrs.add(Attribute.of("ltl", null));
        inputAttrs.add(Attribute.ANYWHERE);

        // rule
        Rule rule = new Rule(inputLhs, inputRhs, context);
        rule.setRequires(inputRequires);
        rule.setEnsures(null);
        rule.setAttributes(inputAttrs);


        // create the output rule
        // LHS
        Variable phi = new Variable("GeneratedFreshVar0", Sort.K);
        Term outputLTLState = WrapVariableWithTopCell.wrapPCAndVarWithGeneratedTop(phi, inputLTLState.shallowCopy());
        KApp outputLTLStateKApp = KApp.of(new KInjectedLabel(outputLTLState), KList.EMPTY);
        Term outpuLhs = KApp.of(KLabelConstant.of(ResolveLtlAttributes.LTL_SAT), outputLTLStateKApp, predicate.shallowCopy());

        // RHS
        Term outputRhs = BoolBuiltin.TRUE;

        // requires
        KApp outputVal = KApp.of(KLabelConstant.of("val"), outputLTLStateKApp, X.shallowCopy());
        KApp defaultTrue = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, BoolBuiltin.TRUE, BoolBuiltin.TRUE);
        Term outputCheckSat = ResolveLtlAttributes.createSMTImplicationTerm(phi, defaultTrue, context);
        Term valEq = KApp.of(KLabelConstant.KEQ, outputVal, I.shallowCopy());
        Term outputRequires = KApp.of(KLabelConstant.ANDBOOL_KLABEL, valEq, BoolBuiltin.TRUE, outputCheckSat);

        // attributes
        Attributes outputAttrs = new Attributes();
        outputAttrs.add(Attribute.of("ltl", null));
        outputAttrs.add(Attribute.ANYWHERE);

        // rule
        Rule outputRule = new Rule(outpuLhs, outputRhs, context);
        outputRule.setRequires(outputRequires);
        outputRule.setEnsures(null);
        outputRule.setAttributes(outputAttrs);


        // test ResolverLTLAttributes transformer
        ResolveLtlAttributes resolveLtlAttributes = new ResolveLtlAttributes(context);
        rule = (Rule) resolveLtlAttributes.visitNode(rule);
        FreshVariableNormalizer normalizer = new FreshVariableNormalizer(context);
        rule = (Rule) normalizer.visitNode(rule);
        Assert.assertEquals(rule.getBody(), outputRule.getBody());
        Assert.assertEquals(rule.getRequires(), outputRule.getRequires());
        Assert.assertEquals(rule.getEnsures(), outputRule.getEnsures());
    }

}
