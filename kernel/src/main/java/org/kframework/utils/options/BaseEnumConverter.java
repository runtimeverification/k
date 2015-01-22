// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils.options;

import java.util.EnumSet;
import java.util.HashSet;
import java.util.Set;

import com.beust.jcommander.ParameterException;
import com.beust.jcommander.converters.BaseConverter;

/**
 * Helper class used to abstract functionality of converting enums in JCommander.
 * We use this because JCommander has bugs and feature issues regarding casing and hyphens
 * in enum names.
 * @author dwightguth
 *
 */
public abstract class BaseEnumConverter<T extends Enum<T>> extends BaseConverter<T> {

    public BaseEnumConverter(String optionName) {
        super(optionName);
    }

    @Override
    public T convert(String arg) {
        try {
            return Enum.valueOf(enumClass(), arg.toUpperCase().replaceAll("-", "_"));
        } catch (IllegalArgumentException e) {
            EnumSet<T> values = EnumSet.allOf(enumClass());
            Set<String> validValues = new HashSet<>();
            for (T value : values) {
                validValues.add(friendlyName(value));
            }
            throw new ParameterException("Invalid value for " + getOptionName() + " parameter. Allowed values:" +
                    validValues);
        }
    }

    public abstract Class<T> enumClass();

    public static String friendlyName(Enum<?> arg) {
        return arg.name().toLowerCase().replaceAll("_", "-");
    }
}
