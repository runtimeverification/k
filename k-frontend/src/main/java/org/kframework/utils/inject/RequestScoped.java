// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.utils.inject;

import static java.lang.annotation.ElementType.METHOD;
import static java.lang.annotation.ElementType.TYPE;
import static java.lang.annotation.RetentionPolicy.RUNTIME;

import com.google.inject.ScopeAnnotation;
import java.lang.annotation.Retention;
import java.lang.annotation.Target;

@Target({TYPE, METHOD})
@Retention(RUNTIME)
@ScopeAnnotation
public @interface RequestScoped {}
