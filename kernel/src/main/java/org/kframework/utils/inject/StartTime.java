// Copyright (c) K Team. All Rights Reserved.
package org.kframework.utils.inject;

import com.google.inject.BindingAnnotation;

import java.lang.annotation.Retention;
import java.lang.annotation.Target;

import static java.lang.annotation.ElementType.*;
import static java.lang.annotation.RetentionPolicy.*;

/**
 * @author Denis Bogdanas
 * Created on 20-Nov-19.
 */
@BindingAnnotation @Target({FIELD, PARAMETER, METHOD}) @Retention(RUNTIME)
public @interface StartTime {}
