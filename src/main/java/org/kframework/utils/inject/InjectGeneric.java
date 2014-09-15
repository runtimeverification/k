// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import static java.lang.annotation.ElementType.FIELD;
import static java.lang.annotation.ElementType.METHOD;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;

import com.google.inject.BindingAnnotation;

@BindingAnnotation @Target({ FIELD, METHOD }) @Retention(RUNTIME)
public @interface InjectGeneric {}
