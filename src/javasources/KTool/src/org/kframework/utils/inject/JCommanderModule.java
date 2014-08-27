// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import static java.lang.annotation.ElementType.FIELD;
import static java.lang.annotation.ElementType.METHOD;
import static java.lang.annotation.ElementType.PARAMETER;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;

import org.kframework.utils.StringUtil;

import com.beust.jcommander.JCommander;
import com.google.inject.AbstractModule;
import com.google.inject.BindingAnnotation;

public class JCommanderModule extends AbstractModule  {

    private final String usage;
    private final String experimentalUsage;

    public JCommanderModule(JCommander jc) {
        StringBuilder sb = new StringBuilder();
        jc.usage(sb);
        this.usage = StringUtil.finesseJCommanderUsage(sb.toString(), jc)[0];
        this.experimentalUsage = StringUtil.finesseJCommanderUsage(sb.toString(), jc)[1];
    }

    @BindingAnnotation @Target({FIELD, PARAMETER, METHOD}) @Retention(RUNTIME)
    public @interface Usage {}
    @BindingAnnotation @Target({FIELD, PARAMETER, METHOD}) @Retention(RUNTIME)
    public @interface ExperimentalUsage {}

    @Override
    protected void configure() {
        bind(String.class).annotatedWith(Usage.class).toInstance(usage);
        bind(String.class).annotatedWith(ExperimentalUsage.class).toInstance(experimentalUsage);
    }
}
