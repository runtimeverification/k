// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.w3c.dom.Element;

/**
 * Abstract KLabel class.
 */
public abstract class KLabel extends Term {

    protected KLabel() {
        super(Sort.KLABEL);
    }

    protected KLabel(Element element) {
        super(element);
        this.sort = Sort.KLABEL;
        //System.out.println(this.sort);
        //assert this.sort.equals(Sort.KLABEL);
    }

    protected KLabel(KLabel kLabel) {
        super(kLabel);
    }
}
