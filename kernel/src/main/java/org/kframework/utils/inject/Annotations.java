// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import java.lang.annotation.Annotation;

public class Annotations {

    public static Main main(Class<? extends Annotation> annotation) {
        return new Main() {

            @Override
            public Class<? extends Annotation> annotationType() {
                return Main.class;
            }

            @Override
            public Class<? extends Annotation> value() {
                return annotation;
            }

            public int hashCode() {
                // This is specified in java.lang.Annotation.
                return (127 * "value".hashCode()) ^ annotation.hashCode();
            }

            public boolean equals(Object o) {
                if (!(o instanceof Main)) {
                    return false;
                }
                Main other = (Main) o;
                return annotation.equals(other.value());
            }

        };
    }

    public static Spec1 spec1(Class<? extends Annotation> annotation) {
        return new Spec1() {

            @Override
            public Class<? extends Annotation> annotationType() {
                return Spec1.class;
            }

            @Override
            public Class<? extends Annotation> value() {
                return annotation;
            }

            public int hashCode() {
                // This is specified in java.lang.Annotation.
                return (127 * "value".hashCode()) ^ annotation.hashCode();
            }

            public boolean equals(Object o) {
                if (!(o instanceof Spec1)) {
                    return false;
                }
                Spec1 other = (Spec1) o;
                return annotation.equals(other.value());
            }

        };
    }

    public static Spec2 spec2(Class<? extends Annotation> annotation) {
        return new Spec2() {

            @Override
            public Class<? extends Annotation> annotationType() {
                return Spec2.class;
            }

            @Override
            public Class<? extends Annotation> value() {
                return annotation;
            }

            public int hashCode() {
                // This is specified in java.lang.Annotation.
                return (127 * "value".hashCode()) ^ annotation.hashCode();
            }

            public boolean equals(Object o) {
                if (!(o instanceof Spec2)) {
                    return false;
                }
                Spec2 other = (Spec2) o;
                return annotation.equals(other.value());
            }

        };
    }
}
