// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.IStringConverter;
import com.beust.jcommander.ParameterException;
import java.time.Duration;

/**
 * Converts strings like 10ms/10s/10m/10h to a Duration
 *
 * @author Denis Bogdanas
 */
public class DurationConverter implements IStringConverter<Duration> {

  @Override
  public Duration convert(String value) {
    int num;
    String unit;
    try {
      // kudos to https://stackoverflow.com/a/3552805/4182868
      String numPart = value.split("[a-z]")[0];
      num = Integer.parseInt(numPart);
      unit = value.substring(numPart.length());
    } catch (ArrayIndexOutOfBoundsException | NumberFormatException e) {
      throw durationException(value);
    }
    return switch (unit) {
      case "ms" -> Duration.ofMillis(num);
      case "s" -> Duration.ofSeconds(num);
      case "m" -> Duration.ofMinutes(num);
      case "h" -> Duration.ofHours(num);
      case "d" -> Duration.ofDays(num);
      default -> throw durationException(value);
    };
  }

  private ParameterException durationException(String value) {
    return new ParameterException(
        String.format(
            "Invalid value for duration '%s', valid value examples: 10ms, 10s, 10m, 10h or 10d",
            value));
  }
}
