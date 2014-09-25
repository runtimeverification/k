// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.IValueValidator;
import com.beust.jcommander.ParameterException;

/**
 * Since the default "PositiveInteger" validator actually validates non-negative
 * integers, I created this class as a utility
 * @author dwightguth
 *
 */
public class PositiveInteger implements IValueValidator<Integer> {
    @Override
    public void validate(String name, Integer value) throws ParameterException {
        if (value <= 0) {
            throw new ParameterException("Parameter " + name + " should be positive (found " + value + ")");
        }
    }
}
