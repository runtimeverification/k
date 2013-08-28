package org.kframework.backend.pdmc.pda;

import java.util.Set;

/**
 * @author Traian
 */
public interface PushdownSystemInterface<Control, Alphabet> {
    Configuration<Control, Alphabet> initialConfiguration();
    Set<Rule<Control, Alphabet>> getRules(ConfigurationHead<Control, Alphabet> configurationHead);
}
