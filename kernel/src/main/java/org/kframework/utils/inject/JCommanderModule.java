// Copyright (c) K Team. All Rights Reserved.
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

import com.beust.jcommander.internal.Console;
import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterException;
import com.google.inject.AbstractModule;
import com.google.inject.BindingAnnotation;
import com.google.inject.Provides;

public class JCommanderModule extends AbstractModule  {

    @BindingAnnotation @Target({FIELD, PARAMETER, METHOD}) @Retention(RUNTIME)
    public @interface Usage {}

    @Override
    protected void configure() {
        bind(String[].class).annotatedWith(Options.class)
            .toProvider(SimpleScope.seededKeyProvider()).in(RequestScoped.class);;
    }

    @Provides @RequestScoped
    JCommander jcommander(@Options String[] args, Tool tool, @Options Set<Object> options, KExceptionManager kem, Stopwatch sw) {
        try {
            JCommander jc = new JCommander(options.toArray(new Object[options.size()]), args);
            jc.setProgramName(tool.name().toLowerCase());
            sw.printIntermediate("Parse command line options");
            return jc;
        } catch (ParameterException e) {
            throw KEMException.criticalError(e.getMessage());
        }
    }

    void usage(JCommander jc, StringBuilder sb) {
        Console defaultConsole = jc.getConsole();
        jc.setConsole(new Console() {
            @Override
            public void print(String msg) {
                sb.append(msg);
            }

            @Override
            public void println(String msg) {
                sb.append(msg).append('\n');
            }

            @Override
            public char[] readPassword(boolean echoInput) {
                return defaultConsole.readPassword(echoInput);
            }
        });
        jc.usage();
        jc.setConsole(defaultConsole);
    }

    @Provides @Usage @RequestScoped
    String usage(JCommander jc) {
        StringBuilder sb = new StringBuilder();
        usage(jc, sb);
        //for some reason the usage pattern indents commands inconsistently, so we need to adjust it
        return sb.toString().replaceAll("        ", "    ");
    }
}
