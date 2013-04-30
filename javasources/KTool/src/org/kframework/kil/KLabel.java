package org.kframework.kil;

import org.w3c.dom.Element;


/**
 * Abstract KLabel class.
 */
public abstract class KLabel extends Term {

	protected KLabel() {
        super("KLabel");
    }

    protected KLabel(Element element) {
        super(element);
        this.sort = "KLabel";
    }

    protected KLabel(KLabel kLabel) {
        super(kLabel);
    }

}
