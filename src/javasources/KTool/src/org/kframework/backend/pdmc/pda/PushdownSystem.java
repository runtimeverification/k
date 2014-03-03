package org.kframework.backend.pdmc.pda;

import com.google.common.base.Joiner;

import java.util.*;

/**
 * An implementation of a pushdown system.
 * @see org.kframework.backend.pdmc.pda.PushdownSystemInterface
 *
 * @author TraianSF
 */
public class PushdownSystem<Control, Alphabet> implements PushdownSystemInterface<Control, Alphabet> {
    public PushdownSystem(Collection<Rule<Control, Alphabet>> rules, Configuration<Control, Alphabet> initialState) {
        deltaIndex = new HashMap<>();
        for (Rule<Control, Alphabet> rule : rules) {
            ConfigurationHead<Control, Alphabet> head = rule.getHead();
            Set<Rule<Control, Alphabet>> headRules = deltaIndex.get(head);
            if (headRules == null) {
                headRules = new HashSet<>();
                deltaIndex.put(head, headRules);
            }
            headRules.add(rule);
        }

        setInitialConfiguration(initialState);
    }

    public void setInitialConfiguration(Configuration<Control, Alphabet> initialConfiguration) {
        this.initialConfiguration = initialConfiguration;
    }

    Configuration<Control, Alphabet> initialConfiguration;
    Map<ConfigurationHead<Control, Alphabet>, Set<Rule<Control, Alphabet>>> deltaIndex;

    @Override
    public Configuration<Control, Alphabet> initialConfiguration() {
        return initialConfiguration;
    }

    @Override
    public Set<Rule<Control, Alphabet>> getRules(ConfigurationHead<Control, Alphabet> configurationHead) {
        Set<Rule<Control, Alphabet>> rules = deltaIndex.get(configurationHead);
        if (rules == null) rules = Collections.emptySet();
        return rules;
    }

    public static PushdownSystem<String, String> of(String s) {
        List<Rule<String, String>> rules = new ArrayList<>();
        String[] stringRules = s.split("\\s*;\\s*");

        int n = stringRules.length - 1;
        Configuration<String, String> initialState =  Configuration.of(stringRules[n]);
        for (int i = 0; i < n; i++) {
            Rule<String, String> rule = Rule.of(stringRules[i]);
            rules.add(rule);
        }
        return  new PushdownSystem<>(rules, initialState);
    }

    @Override
    public String toString() {
        Joiner joiner = Joiner.on(";\n");
        StringBuilder builder = new StringBuilder();
        joiner.appendTo(builder, getRules());
        if (initialConfiguration != null) {
            builder.append(";\n");
            builder.append(initialConfiguration.toString());
        }
        return builder.toString();
    }

    private Collection<Rule<Control, Alphabet>> getRules() {
        List<Rule<Control, Alphabet>> rules = new ArrayList<>();
        for (Set<Rule<Control, Alphabet>> values : deltaIndex.values()) {
            rules.addAll(values);
        }
        return rules;
    }
}
