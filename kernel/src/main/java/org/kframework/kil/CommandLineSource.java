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


    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        CommandLineSource that = (CommandLineSource) o;

        if (!optionName.equals(that.optionName)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return optionName.hashCode();
    }
}
