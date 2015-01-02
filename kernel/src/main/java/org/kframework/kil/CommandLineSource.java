// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil;

public class CommandLineSource implements Source {

    private String optionName;

    public CommandLineSource(String optionName) {
        this.optionName = optionName;
    }

    public String getOptionName() {
        return optionName;
    }

    @Override
    public String toString() {
        return "Command line: " + optionName;
    }
}
