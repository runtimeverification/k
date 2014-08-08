package org.kframework.kil;

public class CommandLineSource extends Source {

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
