// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import static java.lang.annotation.ElementType.FIELD;
import static java.lang.annotation.ElementType.METHOD;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;

import com.google.inject.BindingAnnotation;

/**
 * An annotation used to manually inject a generic implementation
 * of a generic interface for all possible type parameters.
 * In order for this to work, it is necessary to use a TypeListener
 * and a MembersInjector directly.
 * @author dwightguth
 *
 */
@BindingAnnotation @Target({ FIELD, METHOD }) @Retention(RUNTIME)
public @interface InjectGeneric {}
