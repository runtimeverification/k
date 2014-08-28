package org.kframework.utils.inject;

import org.kframework.main.Main;
import org.kframework.transformation.Transformation;

import com.google.inject.Injector;
import com.google.inject.Key;
import com.google.inject.TypeLiteral;

public class ProfileInjection {

    public static void main(String[] args) {
        while(true) {
            Injector injector = Main.getInjector(args);
            injector.getInstance(Key.get(new TypeLiteral<Transformation<Void, Void>>() {}));
        }
    }
}
