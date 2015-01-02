// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import static java.lang.annotation.ElementType.METHOD;
import static java.lang.annotation.ElementType.TYPE;

import java.lang.annotation.Retention;

import static java.lang.annotation.RetentionPolicy.RUNTIME;

import java.lang.annotation.Target;

import com.google.inject.ScopeAnnotation;

@Target({ TYPE, METHOD }) @Retention(RUNTIME) @ScopeAnnotation
public @interface DefinitionScoped {}