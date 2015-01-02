// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.backend;

import static java.lang.annotation.ElementType.FIELD;
import static java.lang.annotation.ElementType.METHOD;
import static java.lang.annotation.ElementType.PARAMETER;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;

import org.kframework.compile.utils.CompilerSteps;
import org.kframework.kil.Definition;

import com.google.inject.BindingAnnotation;

public interface Backend {
    public void run(Definition definition);

    public String getDefaultStep();

    /**
     * Applies the first compilation step of this backend to a given definition.
     *
     * @param def
     *            the given definition
     * @return the resulting definition after this compilation step
     */
    Definition firstStep(Definition def);

    /**
     * Applies the last compilation step of this backend to a given definition.
     *
     * @param def
     *            the given definition
     * @return the resulting definition after this compilation step
     */
    Definition lastStep(Definition def);

    public boolean autoinclude();
    public String autoincludedFile();
    public boolean generatesDefinition();

    /**
     * Gets all compilation steps of this backend.
     *
     * @return a compound compilation step consisting of all the compilation
     *         steps
     */
    public CompilerSteps<Definition> getCompilationSteps();
    // TODO(YilongL): why mixing the uses of "compilation step" and
    // "compiler step"? what about a uniform name?

    @BindingAnnotation @Target({ FIELD, PARAMETER, METHOD }) @Retention(RUNTIME)
    public static @interface Autoinclude {}
    @BindingAnnotation @Target({ FIELD, PARAMETER, METHOD }) @Retention(RUNTIME)
    public static @interface AutoincludedFile {}
}
