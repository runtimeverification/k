// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.options;

import java.util.ArrayList;
import java.util.List;

import com.beust.jcommander.IStringConverter;

/**
 * This class is designed to support the specification of a list of strings
 * using a single string in cases where using a list of strings would be
 * infeasible. For example, in krun, simulation options are passed by 
 * passing a set of krun options as parameter to a special krun option.
 * We can't use variable arity because then --simulation --directory foo
 * would be interpreted as two options instead of one with two words.
 * @author dwightguth
 *
 */
public class StringListConverter implements IStringConverter<List<String>> {
    
    @Override
    public List<String> convert(String val) {
        //split on whitespace not preceded by a backslash
        String[] parts = val.split("(?<!\\\\)\\s+"); 
        List<String> result = new ArrayList<>();
        for (String part : parts) {
            result.add(part.trim().replaceAll("\\\\(\\s)", "$1"));
        }
        return result;
    }
    
}