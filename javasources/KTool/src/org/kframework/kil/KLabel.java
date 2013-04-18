package org.kframework.kil;


/**
 * Abstract KLabel class.
 */
public abstract class KLabel extends Term {

	protected KLabel() {
        super("KLabel");
    }

    protected KLabel(KLabel kLabel) {
        super(kLabel);
    }

}
