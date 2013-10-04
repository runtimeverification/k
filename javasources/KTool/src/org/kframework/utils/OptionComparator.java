package org.kframework.utils;

import org.apache.commons.cli.Option;

import java.util.ArrayList;
import java.util.Comparator;

public class OptionComparator implements Comparator<Object> {

    private ArrayList<Option> optionList;

    public OptionComparator(ArrayList<Option> optionList) {
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
