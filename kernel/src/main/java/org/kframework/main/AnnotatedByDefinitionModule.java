// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.main;

import com.google.inject.Binding;
import com.google.inject.Key;
import com.google.inject.Module;
import com.google.inject.PrivateModule;
import com.google.inject.spi.DefaultElementVisitor;
import com.google.inject.spi.Element;
import com.google.inject.spi.Elements;

import java.util.List;

public abstract class AnnotatedByDefinitionModule extends PrivateModule {

    public void exposeBindings(List<Module> modules, Class cls) {
        for (Element element : Elements.getElements(modules)) {
            element.acceptVisitor(new DefaultElementVisitor<Void>() {
                @Override
                public <T> Void visit(Binding<T> binding) {
                    Key<T> key = binding.getKey();
                    if (key.getAnnotation() == null && key.getAnnotationType() == null) {
                        bind(key.getTypeLiteral()).annotatedWith(cls).to(key.getTypeLiteral());
                        expose(key.getTypeLiteral()).annotatedWith(cls);
                    }
                    return null;
                }
            });
        }
        modules.forEach(AnnotatedByDefinitionModule.this::install);
    }
}
