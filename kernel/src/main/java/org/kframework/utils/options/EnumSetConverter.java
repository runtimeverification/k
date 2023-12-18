// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.converters.BaseConverter;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

public abstract class EnumSetConverter<T extends Enum<T>, C extends BaseEnumConverter<T>>
    extends BaseConverter<Set<T>> {

  public EnumSetConverter(String optionName) {
    super(optionName);
  }

  private final StringListConverter converter = new StringListConverter();

  @Override
  public Set<T> convert(String val) {
    List<String> values = converter.convert(val);
    Set<T> set = EnumSet.noneOf(enumConverter().enumClass());
    for (String value : values) {
      T t = enumConverter().convert(value);
      set.add(t);
    }
    return set;
  }

  public abstract C enumConverter();
}
