// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.utils.koreparser;

import org.kframework.attributes.Source;
import org.kframework.kore.K;

/**
 * Created by dwightguth on 11/17/15.
 */
@Deprecated
public class KoreParser {

    public static K parse(String s, Source src) {
        return org.kframework.parser.kore.KoreParser.parse(s, src);
    }
}
