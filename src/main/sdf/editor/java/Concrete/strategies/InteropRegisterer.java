// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package Concrete.strategies;

import org.strategoxt.lang.JavaInteropRegisterer;
import org.strategoxt.lang.Strategy;

/**
 * Helper class for {@link java_strategy_0_0}.
 */
public class InteropRegisterer extends JavaInteropRegisterer {

	public InteropRegisterer() {
		super(new Strategy[] { string_unescape_sort_0_0.instance, string_trim_last_one_0_0.instance, mergeamb_0_0.instance, clear_console_0_0.instance, annolocation_0_0.instance, annolocationremove_0_0.instance, xml_string_escape_from_string_0_0.instance });
	}
}
