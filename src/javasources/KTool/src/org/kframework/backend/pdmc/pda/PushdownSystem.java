package org.kframework.backend.pdmc.pda;

import com.google.common.base.Joiner;

import java.util.*;

/**
 * @author Traian
 */
public class PushdownSystem<Control, Alphabet> implements PushdownSystemInterface<Control, Alphabet> {
    public void setInitialConfiguration(Configuration<Control, Alphabet> initialConfiguration) {
        this.initialConfiguration = initialConfiguration;
    }

    Configuration<Control, Alphabet> initialConfiguration;
    Map<ConfigurationHead<Control, Alphabet>, Set<Rule<Control, Alphabet>>> deltaIndex;

    public PushdownSystem(Collection<Rule<Control, Alphabet>> rules) {
        deltaIndex = new HashMap<ConfigurationHead<Control, Alphabet>, Set<Rule<Control, Alphabet>>>();
        for (Rule<Control, Alphabet> rule : rules) {
            ConfigurationHead<Control, Alphabet> head = rule.getHead();
            Set<Rule<Control, Alphabet>> headRules = deltaIndex.get(head);
            if (headRules == null) {
                headRules = new HashSet<Rule<Control, Alphabet>>();
                deltaIndex.put(head, headRules);
            }
            headRules.add(rule);
        }
    }

//    Set<Configuration<Control, Alphabet>> getTransitions(Configuration<Control, Alphabet> configuration) {
//        if (configuration.isFinal()) return Collections.emptySet();
//        Set<Rule<Control,Alphabet>> rules = deltaIndex.get(configuration.getHead());
//        if (rules == null) return Collections.emptySet();
//        HashSet<Configuration<Control, Alphabet>> configurations = new HashSet<Configuration<Control, Alphabet>>();
//        for (Rule<Control,Alphabet> rule : rules) {
//            configurations.add(new Configuration<Control, Alphabet>(rule.endConfiguration(), configuration.getStack()));
//        }
//        return configurations;
//    }


    @Override
    public Configuration<Control, Alphabet> initialConfiguration() {
        return null;  //To change body of implemented methods use File | Settings | File Templates.
    }

    @Override
    public Set<Rule<Control, Alphabet>> getRules(ConfigurationHead<Control, Alphabet> configurationHead) {
        Set<Rule<Control, Alphabet>> rules = deltaIndex.get(configurationHead);
        if (rules == null) rules = Collections.<Rule<Control, Alphabet>>emptySet();
        return rules;
    }

    public static PushdownSystem<String, String> of(String s) {
        ArrayList<Rule<String, String>> rules = new ArrayList<Rule<String, String>>();
        String[] stringRules = s.split("\\s*;\\s*");
        for (String stringRule : stringRules) {
            Rule<String, String> rule = Rule.of(stringRule);
            rules.add(rule);
        }
        return  new PushdownSystem<String, String>(rules);
    }

    @Override
    public String toString() {
        Joiner joiner = Joiner.on(";\n");
        StringBuilder builder = new StringBuilder();
        joiner.appendTo(builder, getRules());
        return builder.toString();
    }

    private Collection<Rule<Control, Alphabet>> getRules() {
        ArrayList<Rule<Control, Alphabet>> rules = new ArrayList<Rule<Control, Alphabet>>();
        for (Set<Rule<Control, Alphabet>> values : deltaIndex.values()) {
            rules.addAll(values);
        }
        return rules;
    }
}
