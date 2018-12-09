// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.attributes.Location;
import org.kframework.backend.java.kil.Rule;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.util.Collections;
import java.util.Formatter;
import java.util.HashMap;
import java.util.Map;

/**
 * @author Denis Bogdanas
 * Created on 27-Aug-18.
 */
public class RuleSourceUtil {
    private static final Map<Rule, String> cache = Collections.synchronizedMap(new HashMap<>());

    public static boolean sourceShortEnough(Rule rule) {
        Location location = rule.getLocation();
        return location != null && location.endLine() - location.startLine() <= 20;
    }

    public static String loadSource(Rule rule) {
        if (!cache.containsKey(rule)) {
            if (rule.getSource() != null && rule.getLocation() != null) {
                cache.putIfAbsent(rule, FileUtil.loadFragment(new File(rule.getSource().source()), rule.getLocation()));
            }
        }
        return cache.get(rule);
    }

    public static void printSourceAndRule(Rule rule) {
        File source = rule.source().isPresent() ? new File(rule.getSource().source()) : null;
        System.err.format("\nSource: %s %s\n", source, rule.getLocation());
        if (sourceShortEnough(rule)) {
            System.err.println(loadSource(rule));
        } else {
            System.err.println("rule too long or location unknown...");
        }
    }

    public static void printRuleAndSource(Rule rule) {
        appendRuleAndSource(rule, System.err);
    }

    public static void appendRuleAndSource(Rule rule, Appendable out) {
        File source = rule.source().isPresent() ? new File(rule.getSource().source()) : null;
        Formatter formatter = new Formatter(out);
        if (sourceShortEnough(rule)) {
            formatter.format("%s\n", loadSource(rule));
        } else {
            formatter.format("rule too long or location unknown...\n");
        }
        formatter.format("\tSource: %s %s\n\n", source, rule.getLocation());
    }
}
