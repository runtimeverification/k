// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.Cell;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.Map;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimap;


/**
 * Created with IntelliJ IDEA.
 * User: Traian
 * Date: 11/7/13
 * Time: 1:51 PM
 * To change this template use File | Settings | File Templates.
 */
public class ConfigurationSubstitutionVisitor extends BasicVisitor {

    private final Multimap<Term, Term> substitutionMultimap;
    public ConfigurationSubstitutionVisitor(Context context) {
        super(context);
        substitutionMultimap = HashMultimap.create();
    }

    public Map<Term, Term> getSubstitution() {
        Map<Term, Term> substitutionMap = Maps.newHashMap();
        substitutionMultimap.asMap().entrySet().stream().forEach(entry -> {
                if (entry.getValue().size() == 1) {
                    substitutionMap.put(entry.getKey(), entry.getValue().iterator().next());
                }});
        return substitutionMap;
    }

    @Override
    public Void visit(Cell cell, Void _void) {
        super.visit(cell, _void);
        substitutionMultimap.put(
                new Variable(cell.getLabel().toUpperCase().replace("-", ""), context.getCellSort(cell)),
                cell.getContents());
        return null;
    }
}
