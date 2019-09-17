// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.backend.kore;

import org.kframework.attributes.Att;
import org.kframework.builtin.KLabels;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.kore.FoldK;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KLabel;
import org.kframework.utils.errorsystem.KException;
import scala.collection.Set;

public class ConstructorChecks {
    private final Module module;

    public ConstructorChecks(Module m) {
        module = m;
    }

    /**
     * Checks whether a lhs pattern is constructor-based, i.e., an application of a
     * function symbol to a list of constructor terms.
     *
     * @param term
     * @return
     */
    public boolean isConstructorBased(K term) {
        if (term instanceof KApply) {
            return ((KApply) term).klist().items().stream().allMatch(this::isConstructorTerm);
        }
        if (term instanceof KAs) {
            return isConstructorBased(((KAs) term).pattern());
        }
        KException.criticalError("Unexpecting isConstructorBased call on " + term.getClass());
        return false;
    }

    /**
     * Checks whether a pattern is a constructor term, i.e.,
     * it is not formed by means of reducible symbols (functions).
     *
     * @param term
     * @return
     */
    public boolean isConstructorTerm(K term) {
        return (new FoldK<Boolean>() {
            @Override
            public Boolean unit() {
                return true;
            }

            @Override
            public Boolean merge(Boolean a, Boolean b) {
                return a && b;
            }

            @Override
            public Boolean apply(KApply k) {
                return isConstructorLike(k.klabel()) && super.apply(k);
            }
        }).apply(term);
    }

    // the functions below could be moved to a common place and made public

    private boolean isConstructorLike(KLabel klabel) {
        String labelName = klabel.name();
        if (isBuiltinLabel(klabel)) return false;
        if (isInjectionLabel(labelName) || isBuiltinModuloConstructor(klabel)) return true;
        Set<Production> productionSet = module.productionsFor().apply(klabel);
        assert productionSet.size() == 1 : "Should not have more than one production";
        Production production = productionSet.head();
        return !production.att().contains(Att.Function());
    }

    public static boolean isBuiltinLabel(KLabel label) {
        return label.name().equals(KLabels.ML_FALSE.name()) || label.name().equals(KLabels.ML_TRUE.name()) || label.name().equals(KLabels.ML_NOT.name()) ||
               label.name().equals(KLabels.ML_OR.name()) || label.name().equals(KLabels.ML_AND.name()) || label.name().equals(KLabels.ML_IMPLIES.name()) ||
               label.name().equals(KLabels.ML_EQUALS.name()) || label.name().equals(KLabels.ML_CEIL.name()) || label.name().equals(KLabels.ML_FLOOR.name()) ||
               label.name().equals(KLabels.ML_EXISTS.name()) || label.name().equals(KLabels.ML_FORALL.name()) || label.name().equals(KLabels.CTL_AG.name()) ||
               label.name().equals(KLabels.RL_wEF.name());
    }

    private boolean isBuiltinModuloConstructor(KLabel label) {
        return  label.equals(KLabels.DotMap) || label.equals(KLabels.Map) || label.equals(KLabels.MapItem) ||
                label.equals(KLabels.DotList) || label.equals(KLabels.List) || label.equals(KLabels.ListItem) ||
                label.equals(KLabels.DotSet) || label.equals(KLabels.Set) || label.equals(KLabels.SetItem);
    }

    private boolean isInjectionLabel(String labelName) {
        return labelName.equals(KLabels.INJ);
    }


}
