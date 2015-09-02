// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.inject.AbstractModule;
import com.google.inject.Injector;
import com.google.inject.Provider;
import com.google.inject.Provides;
import com.google.inject.multibindings.MapBinder;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.Builtins;

import java.io.IOException;
import java.lang.invoke.MethodHandle;
import java.lang.invoke.MethodHandles;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.HashMap;
import java.util.Map;
import java.util.Properties;

public class JavaSymbolicCommonModule extends AbstractModule {

    private static final String HOOK_PROPERTIES_FILE_NAME = "/org/kframework/backend/java/symbolic/hooks.properties";

    @Override
    protected void configure() {
        /* initialize {@code table} */
        Properties properties = new Properties();

        try {
            FileUtil.loadProperties(properties, getClass(), HOOK_PROPERTIES_FILE_NAME);
        } catch (IOException e) {
            throw KEMException.internalError("Could not read from resource " + HOOK_PROPERTIES_FILE_NAME, e);
        }

        MapBinder<String, String> builtinMethods = MapBinder.newMapBinder(binder(),
                String.class, String.class, Builtins.class);
        for (Object o: properties.keySet()) {
            String key = (String) o;
            builtinMethods.addBinding(key).toInstance(properties.getProperty(key));
        }
    }

    /**
     * Anything you inject via the injector should be unit tested to avoid failure at runtime. That means
     * ensuring that all dependencies declared in hooks.properties are satisfied.
     */
    @Provides @Builtins
    Map<String, Provider<MethodHandle>> getBuiltinTable(@Builtins Map<String, String> hookDeclarations, Injector injector, KExceptionManager kem) {
        Map<String, Provider<MethodHandle>> result = new HashMap<>();
        MethodHandles.Lookup lookup = MethodHandles.lookup();
        for (String key : hookDeclarations.keySet()) {
            String hook = hookDeclarations.get(key);
            try {
                String className = hook.substring(0, hook.lastIndexOf('.'));
                String methodName = hook.substring(hook.lastIndexOf('.') + 1);
                Class<?> c = Class.forName(className);
                for (Method method : c.getDeclaredMethods()) {
                    if (method.getName().equals(methodName)) {
                        MethodHandle handle = lookup.unreflect(method);
                        result.put(key, () -> {
                            MethodHandle resultHandle = handle;
                            if (!Modifier.isStatic(method.getModifiers())) {
                                try {
                                    resultHandle = MethodHandles.insertArguments(handle, 0, injector.getInstance(c));
                                } catch (KEMException e) {
                                    e.exception.addTraceFrame("while constructing implementation for " + hook + " hook.");
                                    throw e;
                                }
                            }
                            return resultHandle;
                        });
                        break;
                    }
                }
            } catch (ClassNotFoundException | SecurityException | IllegalAccessException e) {
                kem.registerCriticalWarning("missing implementation for hook " + key + ":\n" + hook, e);
            }
        }
        return result;
    }
}
