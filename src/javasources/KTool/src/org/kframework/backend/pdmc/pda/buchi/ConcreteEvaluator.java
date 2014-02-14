package org.kframework.backend.pdmc.pda.buchi;

import com.google.common.base.Joiner;
import org.kframework.backend.pdmc.pda.Configuration;
import org.kframework.backend.pdmc.pda.ConfigurationHead;

import java.util.*;

/**
 * Created by Traian on 04.02.2014.
 */
public class ConcreteEvaluator<Control, Alphabet> implements Evaluator<ConfigurationHead<Control, Alphabet>> {


    public ConcreteEvaluator(Map<ConfigurationHead<Control, Alphabet>, Set<String>> evaluationMap) {
        this.evaluationMap = evaluationMap;
    }

    @Override
    public boolean evaluate(Identifier id) {
        return currentAtoms.contains(id.name);
    }

    @Override
    public void setState(ConfigurationHead<Control, Alphabet> controlAlphabetConfigurationHead) {
        currentAtoms = evaluationMap.get(controlAlphabetConfigurationHead);
        if (null == currentAtoms) currentAtoms = Collections.EMPTY_SET;
    }

    Map<ConfigurationHead<Control, Alphabet>, Set<String>> evaluationMap;
    Set<String> currentAtoms = null;

    public static ConcreteEvaluator<String,String> of(String s) {
        Map<ConfigurationHead<String, String>, Set<String>> evaluationMap = new HashMap<>();
        String[] stringSats = s.split("\\s*;\\s*");
        for (String stringSat : stringSats) {
            String[] stateAndAtoms = stringSat.split("\\s*\\|=\\s*");
            assert stateAndAtoms.length == 2 : "state |= atoms";
            Configuration<String, String> cfg = Configuration.of(stateAndAtoms[0]);
            assert cfg.getStack().empty() : "Should be a configuration head.";
            String[] stringAtoms = stateAndAtoms[1].split("\\s+");
            Set<String> atoms = new HashSet<>();
            for (String stringAtom : stringAtoms) {
                atoms.add(stringAtom);
            }
            evaluationMap.put(cfg.getHead(),atoms);
        }
        return new ConcreteEvaluator<>(evaluationMap);
    }

    @Override
    public String toString() {
        StringBuilder stringBuilder = new StringBuilder();
        for (Map.Entry<ConfigurationHead<Control, Alphabet>, Set<String>> entry : evaluationMap.entrySet()) {
            stringBuilder.append(entry.getKey().toString());
            stringBuilder.append(" |= ");
            Joiner joiner = Joiner.on(' ');
            joiner.appendTo(stringBuilder, entry.getValue());
            stringBuilder.append(";\n");
        }
        return stringBuilder.toString();
    }
}
