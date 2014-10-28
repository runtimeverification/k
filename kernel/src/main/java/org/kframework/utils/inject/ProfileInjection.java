// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import java.io.File;
import java.util.Arrays;

import org.kframework.main.Main;
import org.kframework.transformation.Transformation;

import com.google.inject.Injector;
import com.google.inject.Key;
import com.google.inject.TypeLiteral;

public class ProfileInjection {

    public static void main(String[] args) {
        while(true) {
            String[] args2 = Arrays.copyOfRange(args, 1, args.length);
            Injector injector = Main.getInjector(args[0], args2);
            injector.getInstance(Key.get(new TypeLiteral<Transformation<Void, Void>>() {}));
        }
    }
}
