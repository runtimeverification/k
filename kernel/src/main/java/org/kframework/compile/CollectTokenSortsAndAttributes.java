// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.backend.kore.RuleInfo;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.kore.KORE;
import org.kframework.kore.Sort;
import org.kframework.kore.SortHead;
import org.kframework.utils.errorsystem.KEMException;
import scala.Tuple2;

import java.util.Objects;

import static org.kframework.Collections.*;

public class CollectTokenSortsAndAttributes {
    private final Module module;
    private final boolean heatCoolEq;

    public CollectTokenSortsAndAttributes(Module m, boolean heatCoolEquations) {
        this.module = m;
        this.heatCoolEq = heatCoolEquations;
    }

    public synchronized Module collect(Module m) {
        // This pass only applies to the main module
        if (!Objects.equals(m.name(), module.name()))
           return m;

        collect();
        return module;
    }

    public Module collect() {
        // Map attribute name to whether the attribute has a value
        module.addAttToAttributesMap(Att.NAT(), true);
        module.addAttToAttributesMap(Att.TERMINALS(), true);
        module.addAttToAttributesMap(Att.COLORS(), true);
        module.addAttToAttributesMap(Att.PRIORITY(), true);

        for (SortHead sort : iterable(module.sortedDefinedSorts())) {
            Att att = module.sortAttributesFor().get(sort).getOrElse(KORE::Att);
            if (att.contains(Att.TOKEN())) {
                module.addTokenSort(sort);
            }
            collectAttributes(att);
        }
        for (Production prod : iterable(module.sortedProductions())) {
            Att att = prod.att();
            if (att.contains(Att.TOKEN())) {
                module.addTokenSort(prod.sort().head());
            }
            collectAttributes(att);
        }
        for (Rule r : iterable(module.sortedRules())) {
            Att att = r.att();
            collectAttributes(att);
            Sort topCellSort = Sorts.GeneratedTopCell();
            String topCellSortStr = "Sort" + topCellSort + "{}";
            RuleInfo ruleInfo = RuleInfo.getRuleInfo(r, heatCoolEq, topCellSortStr, module, null);
            // only collect priorities of semantics rules
            if (!ruleInfo.isEquation() && !ruleInfo.isKore() && !ExpandMacros.isMacro(r)) {
                module.addRulePriority(module.getPriority(att));
            }
        }

        return module;
    }

    private void collectAttributes(Att att) {
        for (Tuple2<Tuple2<Att.Key, String>, ?> attribute : iterable(att.withUserGroupsAsGroupAtt().att())) {
            Att.Key name = attribute._1._1;
            Object val = attribute._2;
            String strVal = val.toString();
            if (strVal.equals("")) {
                if (!module.hasAttributesMap().contains(name)) {
                    module.addAttToAttributesMap(name, false);
                }
            } else {
                module.addAttToAttributesMap(name, true);
            }
        }
    }
}
