// Copyright (c) 2014-2015 K Team. All Rights Reserved.
// This is a modified version of
// https://github.com/indy256/codelibrary/blob/master/java/src/SCCTarjan.java
// which is licensed under the Unlicense http://unlicense.org/UNLICENSE

package org.kframework.utils.algorithms;

import java.util.*;

// optimized version of http://en.wikipedia.org/wiki/Tarjan's_strongly_connected_components_algorithm
public class SCCTarjan {
    int time;
    List<Integer>[] graph;
    int[] lowlink;
    boolean[] used;
    List<Integer> stack;
    List<List<Integer>> components;

    public List<List<Integer>> scc(List<Integer>[] graph) {
        int n = graph.length;
        this.graph = graph;
        lowlink = new int[n];
        used = new boolean[n];
        stack = new ArrayList<>();
        components = new ArrayList<>();

        for (int u = 0; u < n; u++)
            if (!used[u])
                dfs(u);

        return components;
    }

    void dfs(int u) {
        lowlink[u] = time++;
        used[u] = true;
        stack.add(u);
        boolean isComponentRoot = true;

        for (int v : graph[u]) {
            if (!used[v])
                dfs(v);
            if (lowlink[u] > lowlink[v]) {
                lowlink[u] = lowlink[v];
                isComponentRoot = false;
            }
        }

        if (isComponentRoot) {
            List<Integer> component = new ArrayList<>();
            while (true) {
                int k = stack.remove(stack.size() - 1);
                component.add(k);
                lowlink[k] = Integer.MAX_VALUE;
                if (k == u)
                    break;
            }
            components.add(component);
        }
    }

    // Usage example
    public static void main(String[] args) {
        @SuppressWarnings("unchecked")
        List<Integer>[] g = new List[10];
        for (int i = 0; i < g.length; i++) {
            g[i] = new ArrayList<>();
        }
        g[0].add(1);
        g[0].add(2);
        g[2].add(1);
        g[1].add(2);
        g[3].add(2);
        g[4].add(3);
        g[5].add(4);
        g[6].add(5);
        g[7].add(6);
        g[8].add(9);
        g[9].add(7);


        List<List<Integer>> components = new SCCTarjan().scc(g);
        System.out.println(components);
    }
}
