package org.kframework.utils.options;

import java.util.EnumSet;
import java.util.HashSet;
import java.util.Set;

import com.beust.jcommander.ParameterException;

/**
 * Helper class used to abstract functionality of converting enums in JCommander.
 * We use this because JCommander has bugs and feature issues regarding casing and hyphens
 * in enum names.
 * @author dwightguth
 *
 */
public class BaseEnumConverter<T extends Enum<T>> {

    public T convert(Class<T> cls, String arg) {
        try {
            return Enum.valueOf(cls, arg.toUpperCase().replaceAll("-", "_"));
        } catch (IllegalArgumentException e) {
            EnumSet<T> values = EnumSet.allOf(cls);
            Set<String> validValues = new HashSet<>();
            for (T value : values) {
                validValues.add(friendlyName(value));
            }
            throw new ParameterException("Invalid value for --backend parameter. Allowed values:" +
                    validValues);
        }
    }
    
    public static String friendlyName(Enum arg) {
        return arg.name().toLowerCase().replaceAll("_", "-");
    }
}
