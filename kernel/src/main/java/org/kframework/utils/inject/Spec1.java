// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import com.google.inject.BindingAnnotation;

import java.lang.annotation.Annotation;
import java.lang.annotation.Retention;
import java.lang.annotation.Target;

import static java.lang.annotation.ElementType.*;
import static java.lang.annotation.RetentionPolicy.*;

@BindingAnnotation @Target({ FIELD, PARAMETER, METHOD }) @Retention(RUNTIME)
public @interface Spec1 {
    Class<? extends Annotation> value() default Spec1.class;
}
