// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.Lists;

public class GroupProductionsBySort {

    private final Definition definition;
    private final Map<String, List<Production>> prodsOfSort;
    /* the relation between productions and K label constants is many-to-one */
    private final Map<Production, KLabelConstant> klabelOfProd;

    public GroupProductionsBySort(Definition definition) {
        assert definition != null;
        this.definition = definition;

        ImmutableMap.Builder<String, List<Production>> sort2ProdsBuilder = ImmutableMap.builder();
        Map<String, ImmutableList.Builder<Production>> prodsBuilders = new HashMap<String, ImmutableList.Builder<Production>>();
        klabelOfProd = new HashMap<Production, KLabelConstant>();

        for (KLabelConstant klabel : definition.kLabels())
            for (Production prod : klabel.productions()) {
                // TODO(YilongL): This is not the right way to handle bracket
                // productions; fix it!
                if (prod.containsAttribute(Attribute.BRACKET.getKey()))
                    continue;

                String sort = prod.getSort();
                if (!prodsBuilders.containsKey(sort)) {
                    ImmutableList.Builder<Production> b = ImmutableList.builder();
                    prodsBuilders.put(sort, b);
                }
                prodsBuilders.get(sort).add(prod);
                klabelOfProd.put(prod, klabel);
            }
        for (Entry<String, ImmutableList.Builder<Production>> entry : prodsBuilders.entrySet()) {
            sort2ProdsBuilder.put(entry.getKey(), entry.getValue().build());
        }
        prodsOfSort = sort2ProdsBuilder.build();
    }

    public List<KItem> getProductionsAsTerms(Sort sort, TermContext context) {
        List<KItem> freshTerms = new ArrayList<KItem>();
        List<Production> prods = prodsOfSort.get(sort);
        if (prods != null) {
            for (Production prod : prods) {
                List<Term> items = Lists.newArrayListWithCapacity(prod.getItems().size());
                for (ProductionItem prodItem : prod.getItems())
                    if (prodItem instanceof org.kframework.kil.Sort)
                        items.add(Variable.getFreshVariable(Sort.of(((org.kframework.kil.Sort) prodItem).getName())));
                KItem kitem = KItem.of(klabelOfProd.get(prod), new KList(items), context);
                freshTerms.add(kitem);
            }
        }
        return freshTerms;
    }
}
