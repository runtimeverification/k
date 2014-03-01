package org.kframework.backend.java.indexing;

import org.kframework.backend.java.kil.Definition;

/**
 * Author: OwolabiL
 * Date: 3/1/14
 * Time: 12:45 PM
 */
public class IndexCreator {
    BasicIndex basicIndex;

    public static void build(Definition definition){
        BasicIndex basicIndex = new BasicIndex(definition);
        basicIndex.buildIndex();
    }
}
