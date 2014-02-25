package org.kframework.compile.utils;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

public enum KilProperty {
    NO_CONCRETE_SYNTAX;
    //TODO: add more

    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.TYPE)
    public static @interface DependsOn {
	    KilProperty value();
    }

    @Retention(RetentionPolicy.RUNTIME)
    @Target(ElementType.TYPE)
    public static @interface Provides {
	    KilProperty value();
    }
}
