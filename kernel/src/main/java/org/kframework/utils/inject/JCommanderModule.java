// Copyright (c) 2014-2015 K Team. All Rights Reserved.
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
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.options.SortedParameterDescriptions;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterException;
import com.google.inject.AbstractModule;
import com.google.inject.BindingAnnotation;
import com.google.inject.Provides;

public class JCommanderModule extends AbstractModule  {

    @BindingAnnotation @Target({FIELD, PARAMETER, METHOD}) @Retention(RUNTIME)
    public @interface Usage {}
    @BindingAnnotation @Target({FIELD, PARAMETER, METHOD}) @Retention(RUNTIME)
    public @interface ExperimentalUsage {}

    @Override
    protected void configure() {
        bind(String[].class).annotatedWith(Options.class)
            .toProvider(SimpleScope.seededKeyProvider()).in(RequestScoped.class);;
    }

    @Provides @RequestScoped
    JCommander jcommander(@Options String[] args, Tool tool, @Options Set<Object> options, @Options Set<Class<?>> experimentalOptions, KExceptionManager kem, Stopwatch sw) {
        try {
            JCommander jc = new JCommander(options.toArray(new Object[options.size()]), args);
            jc.setProgramName(tool.name().toLowerCase());
            jc.setParameterDescriptionComparator(new SortedParameterDescriptions(experimentalOptions.toArray(new Class<?>[experimentalOptions.size()])));
            sw.printIntermediate("Parse command line options");
            return jc;
        } catch (ParameterException e) {
            throw KEMException.criticalError(e.getMessage(), e);
        }
    }

    @Provides @Usage @RequestScoped
    String usage(JCommander jc) {
        StringBuilder sb = new StringBuilder();
        jc.usage(sb);
        return StringUtil.finesseJCommanderUsage(sb.toString(), jc)[0];
    }

    @Provides @ExperimentalUsage @RequestScoped
    String experimentalUsage(JCommander jc) {
        StringBuilder sb = new StringBuilder();
        jc.usage(sb);
        return StringUtil.finesseJCommanderUsage(sb.toString(), jc)[1];
    }
}
