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
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sort;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;

public class ProductionsOfSort {

    private static Definition definition;
    private static Map<String, List<Production>> prodsOfSort;
    private static Map<Production, KLabelConstant> klabelOfProd;

    public static void init(Definition definition) {
        assert ProductionsOfSort.definition == null;
        ProductionsOfSort.definition = definition;

        ImmutableMap.Builder<String, List<Production>> sort2ProdsBuilder = ImmutableMap.builder();
        Map<String, ImmutableList.Builder<Production>> prodsBuilders = new HashMap<String, ImmutableList.Builder<Production>>();
        klabelOfProd = new HashMap<Production, KLabelConstant>();

        for (KLabelConstant klabel : definition.kLabels())
            for (Production prod : klabel.productions()) {
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

    public static List<KItem> getProdTermsOf(String sort) {
        assert ProductionsOfSort.definition != null;

        List<KItem> freshTerms = new ArrayList<KItem>();
        for (Production prod : prodsOfSort.get(sort)) {
            ImmutableList.Builder<Term> listBuilder = ImmutableList.builder();
            for (ProductionItem prodItem : prod.getItems())
                if (prodItem instanceof Sort)
                    listBuilder.add(Variable.getFreshVariable(((Sort) prodItem).getName()));
            KItem kitem = new KItem(klabelOfProd.get(prod), new KList(listBuilder.build()), definition.context());
            freshTerms.add(kitem);
        }
        return freshTerms;
    }
}
