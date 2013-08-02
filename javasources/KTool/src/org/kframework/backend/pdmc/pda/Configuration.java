package org.kframework.backend.pdmc.pda;

import org.kframework.backend.java.symbolic.Utils;

import java.util.Stack;

/**
 * @author TraianSF
 */
public class Configuration<Control, Alphabet> {
    ConfigurationHead<Control,Alphabet> head;
    Stack<Alphabet> stack;

    public Configuration(Configuration<Control, Alphabet> configuration, Stack<Alphabet> stack) {
        head = configuration.getHead();
        if (stack.isEmpty()) {
            this.stack = configuration.getStack();
        } else {
            Stack<Alphabet> newStack = new Stack<Alphabet>();
            newStack.addAll(stack);
            newStack.addAll(configuration.getStack());
            if (!head.isProper()) {
                head = new ConfigurationHead<Control, Alphabet>(head.getState(), newStack.pop());
            }
        }
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + head.hashCode();
        hash = hash * Utils.HASH_PRIME + stack.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;

        if (!(obj instanceof Configuration)) return false;

        Configuration configuration = (Configuration) obj;
        return head.equals(configuration.head) && stack.equals(configuration.stack);
     }

    public boolean emptyStack() {
        return !head.isProper();
    }

    public ConfigurationHead<Control,Alphabet> getHead() {
        return head;
    }

    public Stack<Alphabet> getStack() {
        return stack;
    }
}
