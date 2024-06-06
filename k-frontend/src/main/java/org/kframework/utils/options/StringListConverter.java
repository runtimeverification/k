// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.IStringConverter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * This class is designed to support the specification of a list of strings using a single string in
 * cases where using a list of strings would be infeasible. For example, in krun, simulation options
 * are passed by passing a set of krun options as parameter to a special krun option. We can't use
 * variable arity because then --simulation --definition foo would be interpreted as two options
 * instead of one with two words.
 *
 * @author dwightguth
 */
public class StringListConverter implements IStringConverter<List<String>> {

  @Override
  public List<String> convert(String val) {
    // split on whitespace not preceded by a backslash
    String[] parts = val.split("(?<!\\\\)\\s+");
    if (parts.length == 1 && parts[0].isEmpty()) {
      return Collections.emptyList();
    }
    List<String> result = new ArrayList<>();
    for (String part : parts) {
      result.add(part.trim().replaceAll("\\\\(\\s)", "$1"));
    }
    return result;
  }
}
