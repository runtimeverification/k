// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.parser;

import com.beust.jcommander.Parameter;

import org.kframework.parser.InputModes;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.BaseEnumConverter;

@RequestScoped
public final class KReadOptions {

    public KReadOptions() {}

    @Parameter(names={"--input", "-i"}, converter=InputModeConverter.class,
            description="How to parse input. <mode> is either [program|binary|kast|json].")
    public InputModes input = InputModes.PROGRAM;

    public static class InputModeConverter extends BaseEnumConverter<InputModes> {

        public InputModeConverter(String optionName) {
            super(optionName);
        }

        @Override
        public Class<InputModes> enumClass() {
            return InputModes.class;
        }
    }
}
