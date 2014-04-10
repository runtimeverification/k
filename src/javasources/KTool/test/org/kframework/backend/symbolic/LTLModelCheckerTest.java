package org.kframework.backend.symbolic;

import junit.framework.Assert;
import org.junit.Before;
import org.junit.Test;
import org.kframework.kil.Attributes;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSorts;
import org.kframework.kil.Production;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.mockito.Mockito;

import java.util.HashMap;
import java.util.HashSet;
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
        context.productions = Mockito.mock(Map.class);

        Mockito.when(context.productions.get(KLabelConstant.of("'|=LTL"))).thenReturn(null);
        Mockito.when(context.productions.get(KLabelConstant.of("val"))).thenReturn(null);
    }

    @Test
    public void testSymbolicLTLStateRuleTransformer() {

        String inputRule = "rule '_|=Ltl_(# B:Bag (),, eq(X:Id ,, I:Int )) => #token(\"#Bool\", \"true\")() requires '_=K_(val(# B:Bag (),, X:Id ),, I:Int ) [ ltl(null),  anywhere(null)]\n";
        String outputRule = "rule '_|=Ltl_(# <generatedTop> B:Bag <path-condition> GeneratedFreshVar0:K  </path-condition>  </generatedTop> (),, eq(X:Id ,, I:Int )) => #token(\"#Bool\", \"true\")() requires '#andBool('_=K_(val(# <generatedTop> B:Bag <path-condition> GeneratedFreshVar0:K  </path-condition>  </generatedTop> (),, X:Id ),, I:Int ),, #token(\"#Bool\", \"true\")(),, '_==K_('checkSat('_andBool_(GeneratedFreshVar0:K ,, 'notBool_('_andBool_(#token(\"#Bool\", \"true\")(),, #token(\"#Bool\", \"true\")())))),, #token(\"#String\", \"\\\"unsat\\\"\")())) [ ltl(null),  anywhere(null)]\n";

        // create input the rule
        // LHS
        Variable LTLState = new Variable("B", KSorts.BAG);
        KApp LTLStateKApp = KApp.of(new KInjectedLabel(LTLState), KList.EMPTY);
        Variable X = new Variable("X", "Id");
        Variable I = new Variable("I", "Int");
        KApp predicate = KApp.of(KLabelConstant.of("eq"), X, I);
        Term lhs = KApp.of(KLabelConstant.of(ResolveLtlAttributes.LTL_SAT), LTLStateKApp, predicate);

        // RHS
        Term rhs = BoolBuiltin.TRUE;

        // requires
        KApp val = KApp.of(KLabelConstant.of("val"), LTLStateKApp, X.shallowCopy());
        Term requires = KApp.of(KLabelConstant.KEQ, val, I.shallowCopy());

        // attributes
        Attributes attrs = new Attributes();
        attrs.set("ltl", null);
        attrs.set("anywhere", null);

        // rule
        Rule rule = new Rule(lhs, rhs, context);
        rule.setRequires(requires);
        rule.setEnsures(null);
        rule.setAttributes(attrs);

        // test input rule
        Assert.assertEquals(rule.toString().trim(), inputRule.trim());

        // test ResolverLTLAttributes transformer
        ResolveLtlAttributes resolveLtlAttributes = new ResolveLtlAttributes(context);
        try {
            rule = (Rule) rule.accept(resolveLtlAttributes);
            Assert.assertEquals(rule.toString().trim(), outputRule.trim());
        } catch (TransformerException e) {
            Assert.fail();
        }
    }
}
