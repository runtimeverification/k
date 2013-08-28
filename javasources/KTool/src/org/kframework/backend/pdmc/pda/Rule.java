package org.kframework.backend.pdmc.pda;

import com.google.common.base.Joiner;

import java.util.List;
import java.util.Stack;

/**
 * @author Traian
 */
public class Rule<Control, Alphabet> {
    ConfigurationHead<Control, Alphabet> lhs;
    Configuration<Control, Alphabet> rhs;

    public Rule(ConfigurationHead<Control, Alphabet> lhs, Configuration<Control, Alphabet> rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
    }

    public Configuration<Control, Alphabet> endConfiguration() {
        return rhs;
    }

    public Control endState() {
        return rhs.getHead().getState();
    }

    public Stack<Alphabet> endStack() {
        Alphabet letter = rhs.getHead().getLetter();
        if (letter == null) return Configuration.<Alphabet>emptyStack();
        @SuppressWarnings("unchecked")
        Stack<Alphabet> stack = (Stack<Alphabet>) rhs.getStack().clone();
        if (stack == null) {
            stack = new Stack<Alphabet>();
        }
        stack.push(letter);
        return stack;
    }

    public ConfigurationHead<Control, Alphabet> getHead() {
        return lhs;
    }

    public static Rule<String, String> of(String stringRule) {
        String[] sides = stringRule.split("\\s*=>\\s*");
        assert sides.length == 2 : "Rules must be of the form: lhs => rhs";
        Configuration<String, String> lhsConf = Configuration.of(sides[0].trim());
        assert lhsConf.getStack().isEmpty() : "lhs should have a configuration head";
        ConfigurationHead<String, String> lhs = lhsConf.getHead();
        Configuration<String, String> rhs = Configuration.of(sides[1].trim());
        return new Rule<String, String>(lhs, rhs);
    }

    @Override
    public String toString() {
        StringBuilder builder = new StringBuilder();
        builder.append(lhs.toString());
        builder.append(" => ");
        builder.append(rhs.toString());
        return builder.toString();
    }
}
