// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.utils;

import org.kframework.kil.Sentence;

import java.io.Serializable;

/**
 * Created by Radu on 05.06.2014.
 *
 * Stores the contents of each parsed rule and the start location.
 */
public class CachedSentence implements Serializable {
    public final Sentence sentence;
    public final int startLine;
    public final int startColumn;

    public CachedSentence(Sentence sentence, int startLine, int startColumn) {
        this.sentence = sentence;
        this.startLine = startLine;
        this.startColumn = startColumn;
    }
}
