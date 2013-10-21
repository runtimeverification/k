package org.kframework.backend.pdmc.pda.buchi;

import org.kframework.backend.pdmc.pda.ConfigurationHead;

import java.util.Set;

/**
 * @author Traian
 */
interface LTLValuation<Control, Alphabet, Atom> {
    Set<Atom> evaluate(ConfigurationHead<Control, Alphabet> head);
}
