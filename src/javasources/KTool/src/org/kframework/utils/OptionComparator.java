// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.utils;

import org.apache.commons.cli.Option;

import java.util.Comparator;
import java.util.List;

public class OptionComparator implements Comparator<Object> {

    private List<Option> optionList;

    public OptionComparator(List<Option> optionList) {
        this.optionList = optionList;
    }

    public int compare(Object obj1, Object obj2) {
        Option opt1 = (Option) obj1;
        Option opt2 = (Option) obj2;
        int index1 = optionList.indexOf(opt1);
        int index2 = optionList.indexOf(opt2);

        if (index1 > index2)
            return 1;
        else if (index1 < index2)
            return -1;
        else
            return 0;
    }
}
