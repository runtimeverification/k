// Copyright (c) 2015 K Team. All Rights Reserved.
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

    public static Spec spec(Class<? extends Annotation> annotation) {
        return new Spec() {

            @Override
            public Class<? extends Annotation> annotationType() {
                return Spec.class;
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
                if (!(o instanceof Spec)) {
                    return false;
                }
                Spec other = (Spec) o;
                return annotation.equals(other.value());
            }

        };
    }
}
