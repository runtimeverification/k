// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import static java.lang.annotation.ElementType.FIELD;
import static java.lang.annotation.ElementType.METHOD;
import static java.lang.annotation.ElementType.PARAMETER;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;
import java.util.Set;

import org.kframework.main.Tool;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.options.SortedParameterDescriptions;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterException;
import com.google.inject.AbstractModule;
import com.google.inject.BindingAnnotation;
import com.google.inject.Provides;

public class JCommanderModule extends AbstractModule  {

    private final String[] args;

    public JCommanderModule(String[] args) {
        this.args = args;
    }

    @BindingAnnotation @Target({FIELD, PARAMETER, METHOD}) @Retention(RUNTIME)
    public @interface Usage {}
    @BindingAnnotation @Target({FIELD, PARAMETER, METHOD}) @Retention(RUNTIME)
    public @interface ExperimentalUsage {}

    @Override
    protected void configure() {}

    @Provides
    JCommander jcommander(Tool tool, @Options Set<Object> options, @Options Set<Class<?>> experimentalOptions, KExceptionManager kem, Stopwatch sw) {
        try {
            JCommander jc = new JCommander(options.toArray(new Object[options.size()]), args);
            jc.setProgramName(tool.name().toLowerCase());
            jc.setParameterDescriptionComparator(new SortedParameterDescriptions(experimentalOptions.toArray(new Class<?>[experimentalOptions.size()])));
            sw.printIntermediate("Parse command line options");
            return jc;
        } catch (ParameterException e) {
            throw KExceptionManager.criticalError(e.getMessage(), e);
        }
    }

    @Provides @Usage
    String usage(JCommander jc) {
        StringBuilder sb = new StringBuilder();
        jc.usage(sb);
        return StringUtil.finesseJCommanderUsage(sb.toString(), jc)[0];
    }

    @Provides @ExperimentalUsage
    String experimentalUsage(JCommander jc) {
        StringBuilder sb = new StringBuilder();
        jc.usage(sb);
        return StringUtil.finesseJCommanderUsage(sb.toString(), jc)[1];
    }
}
