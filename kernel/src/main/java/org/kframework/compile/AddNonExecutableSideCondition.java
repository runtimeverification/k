package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;

import static org.kframework.definition.Constructors.*;

public class AddNonExecutableSideCondition {
    public static Sentence add(Sentence s) {
        if(s instanceof Rule && s.att().contains(Att.NON_EXECUTABLE())) {
            if(((Rule) s).requires() == BooleanUtils.TRUE) {
                s = Rule(((Rule) s).body(), BooleanUtils.FALSE, ((Rule) s).ensures(), s.att());
            }
        }
        return s;
    }
}
