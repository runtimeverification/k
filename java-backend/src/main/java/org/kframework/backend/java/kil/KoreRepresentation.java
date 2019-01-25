// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;


public interface KoreRepresentation {
    /**
     * Returns a KORE (KLabel/KList) representation of this backend object.
     */
    Term toKore();
}
