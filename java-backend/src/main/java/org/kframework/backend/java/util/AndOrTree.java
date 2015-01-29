// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import java.util.Collections;
import java.util.List;

import org.apache.commons.collections4.ListUtils;

import com.google.common.base.Joiner;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.Lists;

public class AndOrTree<T> {
    public static enum NodeType {
        AND,
        OR,
        LEAF
    }

    private final NodeType nodeType;
    private final T leaf;
    private final ImmutableList<AndOrTree<T>> children;

    public ImmutableList<AndOrTree<T>> getChildren() {
        return children;
    }

    public NodeType getNodeType() {
        return nodeType;
    }

    public T getLeaf() {
        return leaf;
    }

    public AndOrTree(T leaf) {
        this.nodeType = NodeType.LEAF;
        this.leaf = leaf;
        this.children = null;
    }

    @SafeVarargs
    public AndOrTree(boolean and, AndOrTree<T>... children) {
        this.nodeType = and ? NodeType.AND : NodeType.OR;
        this.leaf = null;
        this.children = ImmutableList.copyOf(children);
    }

    public AndOrTree(boolean and, Iterable<AndOrTree<T>> children) {
        this.nodeType = and ? NodeType.AND : NodeType.OR;
        this.leaf = null;
        this.children = ImmutableList.copyOf(children);
    }

    public List<List<T>> sumOfProducts() {
        if (nodeType == NodeType.LEAF) {
            return Collections.singletonList(Collections.singletonList(leaf));
        } else if (nodeType == NodeType.OR) {
            List<List<T>> result = Lists.newArrayList();
            for (AndOrTree<T> child : children) {
                //(ab + cd) + (ef + gh) = ab + cd + ef + gh
                result.addAll(child.sumOfProducts());
            }
            return result;
        } else if (nodeType == NodeType.AND) {
            List<AndOrTree<T>> copyOfChildren = Lists.newArrayList(children);
            AndOrTree<T> head = children.get(0);
            copyOfChildren.remove(head);
            if (copyOfChildren.size() == 1) {
                return sumOfProducts(head, copyOfChildren.get(0));
            }
            AndOrTree<T> tail = new AndOrTree<>(true, copyOfChildren);
            return sumOfProducts(head, tail);
        } else {
            throw new AssertionError("unexpected node type");
        }
    }

    private List<List<T>> sumOfProducts(AndOrTree<T> head, AndOrTree<T> tail) {
        List<List<T>> headSumOfProducts = head.sumOfProducts();
        List<List<T>> tailSumOfProducts = tail.sumOfProducts();
        //(ab + cd)(ef + gh) = abef + abgh + cdef + cdgh
        List<List<T>> result = Lists.newArrayList();
        for (List<T> product1 : headSumOfProducts) {
            for (List<T> product2 : tailSumOfProducts) {
                result.add(ListUtils.union(product1, product2));
            }
        }
        return result;
    }

    @Override
    public String toString() {
        switch (nodeType) {
        case LEAF:
            return leaf.toString();
        case AND:
            return "(" + Joiner.on(" /\\ ").join(children) + ")";
        case OR:
            return "(" + Joiner.on(" \\/ ").join(children) + ")";
        default:
            throw new AssertionError("unexpected node type");
        }
    }
}
