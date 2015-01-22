// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;


import java.io.Serializable;

/**
 * @author AndreiS
 */
public interface Index extends Serializable {

    public boolean isUnifiable(Index index);

}
