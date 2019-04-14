// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.attributes.Location;
import org.kframework.backend.java.kil.Rule;
import org.kframework.utils.IndentingFormatter;
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

    private static boolean sourceShortEnough(Rule rule) {
        Location location = rule.getLocation();
        return location != null && location.endLine() - location.startLine() <= 20;
    }

    private static String loadSource(Rule rule) {
        if (!cache.containsKey(rule)) {
            if (rule.getSource() != null && rule.getLocation() != null) {
                cache.putIfAbsent(rule, FileUtil.loadFragment(new File(rule.getSource().source()), rule.getLocation()));
            }
        }
        return cache.get(rule);
    }

    public static void printRuleAndSource(Rule rule) {
        appendRuleAndSource(rule, System.err);
    }

    public static void appendRuleAndSource(Rule rule, Appendable out) {
        appendRuleAndSource(rule, new Formatter(out));
    }

    public static void appendRuleAndSource(Rule rule, Formatter formatter) {
        File source = rule.source().isPresent() ? new File(rule.getSource().source()) : null;
        if (sourceShortEnough(rule)) {
            formatter.format("%s\n", loadSource(rule));
        } else if (rule.source().isPresent()) {
            formatter.format("rule too long...\n");
        } else {
            formatter.format("Rule with no source. toString() format:\n%s\n", rule.toString());
        }
        formatter.format("\tSource: %s %s\n", source, rule.getLocation());
    }

    public static void appendRuleAndSource(Rule rule, IndentingFormatter formatter) {
        File source = rule.source().isPresent() ? new File(rule.getSource().source()) : null;
        if (sourceShortEnough(rule)) {
            formatter.format("%s\n", loadSource(rule));
        } else if (rule.source().isPresent()) {
            formatter.format("rule too long...\n");
        } else {
            formatter.format("Rule with no source. toString() format:\n%s\n", rule.toString());
        }
        formatter.format("\tSource: %s %s\n", source, rule.getLocation());
    }
}
