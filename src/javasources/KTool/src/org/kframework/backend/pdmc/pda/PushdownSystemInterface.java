package org.kframework.backend.pdmc.pda;

import java.util.Set;


/**
 * A minimal interface specifying a pushdown system.
 * @see org.kframework.backend.pdmc.pda.Configuration
 * @see org.kframework.backend.pdmc.pda.ConfigurationHead
 * @see org.kframework.backend.pdmc.pda.Rule
 *
 * @param <Control>  representing the states of a PDS
 * @param <Alphabet> representing the stack alphabet of the PDS
 *
 * @author TraianSF
 */
public interface PushdownSystemInterface<Control, Alphabet> {
    /**
     * @return the initial configuration of a pushdown system (state and initial stack)
     */
    Configuration<Control, Alphabet> initialConfiguration();

    /**
     * Retrieves the rules of the pushdown system for a given configuration head.
     *
     * @param configurationHead the head of configuration for which rules are requested
     * @return the rules of the pushdown system having as head configurationHead
     */
    Set<Rule<Control, Alphabet>> getRules(ConfigurationHead<Control, Alphabet> configurationHead);
}
