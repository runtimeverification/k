package org.kframework.backend.pdmc.pda.buchi;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.pdmc.pda.PushdownSystemInterface;

/**
 * Created by Traian on 07.02.2014.
 */
public interface BuchiPushdownSystemInterface<Control, Alphabet> extends PushdownSystemInterface<Pair<Control, BuchiState>, Alphabet> {

    boolean isFinal(Pair<Control, BuchiState> state);
}
