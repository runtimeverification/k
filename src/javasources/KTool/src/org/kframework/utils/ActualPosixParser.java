// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.utils;

import org.apache.commons.cli.Option;
import org.apache.commons.cli.ParseException;
import org.apache.commons.cli.PosixParser;

import java.util.ListIterator;

public class ActualPosixParser extends PosixParser {

    @Override
    @SuppressWarnings("unchecked")
    public void processArgs(Option opt, ListIterator iter) throws ParseException {
        //whoever wrote Util.stripLeadingAndTrailingQuotes knows about
        //as much about shell scripting as a fish. So we have to override this
        //method and double every double quote at the beginning and end of the
        //string.
        int i = 0;
        while(iter.hasNext()) {
            String str = (String)iter.next();
            if (str.startsWith("\"")) {
                str = "\"" + str;
            }
            if (str.endsWith("\"")) {
                str += "\"";
            }
            iter.set(str);
            i++;
        }
        for (;i > 0;i--) {
            iter.previous();
        }
        super.processArgs(opt, iter);
    }
}
