// Copyright (c) K Team. All Rights Reserved.
package org.kframework.backend.kore;

import org.kframework.attributes.Att;
import org.kframework.compile.RewriteToTop;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.RuleOrClaim;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;

import java.util.function.Function;
import java.util.List;
import java.util.stream.Collectors;


import static org.kframework.Collections.*;

public class RuleInfo {
    boolean isEquation;
    boolean isOwise;
    boolean isKore;
    boolean isCeil;
    Production production;
    String productionSortStr;
    List<Sort> prodChildrenSorts;
    KLabel productionLabel;
    List<K> leftChildren;

    public RuleInfo(boolean equation, boolean owise, boolean kore, boolean ceil, Production production,
                    String prodSortStr, List<Sort> prodChildrenSorts, KLabel prodLabel, List<K> leftChildren) {
        this.isEquation = equation;
        this.isOwise = owise;
        this.isKore = kore;
        this.isCeil = ceil;
        this.production = production;
        this.productionSortStr = prodSortStr;
        this.prodChildrenSorts = prodChildrenSorts;
        this.productionLabel = prodLabel;
        this.leftChildren = leftChildren;
    }

    public static RuleInfo getRuleInfo(RuleOrClaim rule, boolean heatCoolEq, String topCellSortStr, Module module, Function<Sort, String> getSortStr) {
        boolean equation = false;
        boolean owise = false;
        boolean kore = rule.att().contains(Att.KORE());
        boolean ceil = false;
        Production production = null;
        Sort productionSort = null;
        String productionSortStr = null;
        List<Sort> productionSorts = null;
        KLabel productionLabel = null;
        List<K> leftChildren = null;

        K left = RewriteToTop.toLeft(rule.body());
        K leftPattern = left;
        while (leftPattern instanceof KAs) {
            leftPattern = ((KAs)leftPattern).pattern();
        }
        if (leftPattern instanceof KApply) {
            production = module.production((KApply) leftPattern, true);
            productionSort = production.sort();
            if (getSortStr != null) {
                productionSortStr = getSortStr.apply(productionSort);
            } else {
                productionSortStr = productionSort.toString(); // TODO: this is a hack, as we don't use productionSortStr anywhere in this case
            }
            productionSorts = stream(production.items())
                    .filter(i -> i instanceof NonTerminal)
                    .map(i -> (NonTerminal) i)
                    .map(NonTerminal::sort).collect(Collectors.toList());
            productionLabel = production.klabel().get();
            if (productionLabel.name().equals("#Ceil") && rule.att().contains(Att.SIMPLIFICATION())) {
                ceil = true;
            }
            if (production.att().contains(Att.FUNCTION()) || rule.att().contains(Att.SIMPLIFICATION()) || rule.att().contains(Att.ANYWHERE()) && !kore) {
                leftChildren = ((KApply) leftPattern).items();
                equation = true;
            } else if ((rule.att().contains(Att.HEAT()) || rule.att().contains(Att.COOL())) && heatCoolEq) {
                equation = true;
                productionSortStr = topCellSortStr;
            }
            owise = rule.att().contains(Att.OWISE());
        }

        return new RuleInfo(equation, owise, kore, ceil, production,
                productionSortStr, productionSorts, productionLabel, leftChildren);
    }

    public boolean isEquation() {
        return isEquation;
    }

    public boolean isKore() {
        return isKore;
    }

}

