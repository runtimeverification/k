package org.kframework.backend.pdmc.pda;

import java.util.List;

/**
 * @author Traian
 */
public class Rule<Control, Alphabet> {
    ConfigurationHead<Control, Alphabet> lhs;
    Configuration<Control, Alphabet> rhs;

    public Configuration<Control, Alphabet> endConfiguration() {
        return rhs;
    }
}
