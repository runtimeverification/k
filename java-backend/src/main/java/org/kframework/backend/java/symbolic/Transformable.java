// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.JavaSymbolicObject;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/26/13
 * Time: 4:16 PM
 * To change this template use File | Settings | File Templates.
 */
public interface Transformable {
    JavaSymbolicObject accept(Transformer transformer);
}
