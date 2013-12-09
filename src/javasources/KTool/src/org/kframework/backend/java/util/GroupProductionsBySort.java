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
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sort;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;

public class GroupProductionsBySort {

    private final Definition definition;
    private final Map<String, List<Production>> prodsOfSort;
    private final Map<Production, KLabelConstant> klabelOfProd;

    public GroupProductionsBySort(Definition definition) {
        assert definition != null;
        this.definition = definition;

        ImmutableMap.Builder<String, List<Production>> sort2ProdsBuilder = ImmutableMap.builder();
        Map<String, ImmutableList.Builder<Production>> prodsBuilders = new HashMap<String, ImmutableList.Builder<Production>>();
        klabelOfProd = new HashMap<Production, KLabelConstant>();

        for (KLabelConstant klabel : definition.kLabels())
            for (Production prod : klabel.productions()) {
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

    public List<KItem> getProductionsAsTerms(String sort) {
        List<KItem> freshTerms = new ArrayList<KItem>();
        List<Production> prods = prodsOfSort.get(sort);
        if (prods != null) {
            for (Production prod : prods) {
                ImmutableList.Builder<Term> listBuilder = ImmutableList.builder();
                for (ProductionItem prodItem : prod.getItems())
                    if (prodItem instanceof Sort)
                        listBuilder.add(Variable.getFreshVariable(((Sort) prodItem).getName()));
                KItem kitem = new KItem(klabelOfProd.get(prod), new KList(listBuilder.build()), definition.context());
                freshTerms.add(kitem);
            }
        }
        return freshTerms;
    }
}
