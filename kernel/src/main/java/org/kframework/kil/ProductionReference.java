// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Constants;
import org.w3c.dom.Element;

import java.util.Map;

/**
 * Created by Radu on 26.08.2014.
 */
public abstract class ProductionReference extends Term {
    protected final Production production;

    public ProductionReference(Element element, Map<String, Production> conses) {
        super(element);
        this.production = conses.get(element.getAttribute(Constants.CONS_cons_ATTR));
    }

    public ProductionReference(Sort sort, Production production) {
        super(sort);
        this.production = production;
    }

    public ProductionReference(ProductionReference pr) {
        super(pr);
        this.production = pr.production;
    }

    public Production getProduction() {
        return production;
    }
}
