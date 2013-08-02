package org.kframework.backend.pdmc.pda;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * @author Traian
 */
public class PushdownSystem<Control, Alphabet> {
    Map<ConfigurationHead<Control, Alphabet>, Set<Rule<Control, Alphabet>>> deltaIndex;

    Set<Configuration<Control, Alphabet>> getTransitions(Configuration configuration) {
        if (configuration.emptyStack()) return Collections.emptySet();
        Set<Rule<Control,Alphabet>> rules = deltaIndex.get(configuration.getHead());
        if (rules == null) return Collections.emptySet();
        HashSet<Configuration<Control, Alphabet>> configurations = new HashSet<Configuration<Control, Alphabet>>();
        for (Rule<Control,Alphabet> rule : rules) {
            configurations.add(new Configuration<Control, Alphabet>(rule.endConfiguration(), configuration.getStack()));
        }
        return configurations;
    }

}
