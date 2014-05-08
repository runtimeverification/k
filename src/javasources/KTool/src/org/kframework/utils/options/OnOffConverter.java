// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.ParameterException;
import com.beust.jcommander.converters.BaseConverter;

public class OnOffConverter extends BaseConverter<Boolean> {
    
    public OnOffConverter(String optionName) {
        super(optionName);
    }
    
    @Override
    public Boolean convert(String arg0) {
        if (arg0.equals("on")) {
            return true;
        } else if (arg0.equals("off")) {
            return false;
        } else {
            throw new ParameterException("\"" + getOptionName() + "\": must be either \"on\" or \"off\".");
        }
    }
}
