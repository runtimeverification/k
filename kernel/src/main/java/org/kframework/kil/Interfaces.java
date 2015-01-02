// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil;

public class Interfaces {
    private Interfaces() {}

    public interface Collection<T extends ASTNode, E extends Enum<?>> {
        public java.util.Collection<T> getChildren(E type);
    }

    public interface List<T extends ASTNode, E extends Enum<?>> extends Collection<T, E> {
        @Override
        public java.util.List<T> getChildren(E type);
    }

    public interface MutableList<T extends ASTNode, E extends Enum<?>> extends List<T, E> {
        public void setChildren(java.util.List<T> children, E cls);
    }

    public interface Parent<Child extends ASTNode, E extends Enum<?>> {
        public Child getChild(E type);
    }

    public interface MutableParent<Child extends ASTNode, E extends Enum<?>> extends Parent<Child, E> {
        public void setChild(Child child, E type);
    }
}