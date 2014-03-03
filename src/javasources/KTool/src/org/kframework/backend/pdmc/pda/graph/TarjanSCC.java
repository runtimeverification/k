package org.kframework.backend.pdmc.pda.graph;

import java.util.*;

/**
 * A graph class designed for performing Tarjan's SCC algorithm on it.
 *
 * @see <a href="http://en.wikipedia.org/wiki/Tarjan's_strongly_connected_components_algorithm">The rendition on
 * Wikipedia of Tarjan's Strongly Connected Components algorithm.</a>
 *
 * @author TraianSF
 */
public class TarjanSCC<Data, Label> {
    Map<Data,TarjanSCCVertex> vertexSet;
    Map<Data, Map<Data, Label>> edgeSet;

    public TarjanSCC() {
        vertexSet = new HashMap<>();
        edgeSet = new HashMap<>();
        sccs = null;
    }

    /**
     * Indexing class for graph vertices specialized for Tarjan's SCC algorithm
     */
    public class TarjanSCCVertex {

        TarjanSCCVertex(Data data) {
            this.data = data;
            nextVertex = edgeSet.get(data);
            if (nextVertex == null) {
                nextVertex = new HashMap<>();
                edgeSet.put(data, nextVertex);
            }
            index = -1;
            lowlink = -1;
            inStack = false;
        }

        Data data;
        Map<Data, Label> nextVertex;
        int index;
        int lowlink;
        boolean inStack;

        @Override
        public String toString() {
            return data.toString();
        }
    }

    public boolean addEdge(Data data1, Data data2, Label l) {
        TarjanSCCVertex vertex1 = vertexSet.get(data1);
        if (vertex1 == null) {
            vertex1 = new TarjanSCCVertex(data1);
            vertexSet.put(data1, vertex1);
        }
        TarjanSCCVertex vertex2 = vertexSet.get(data2);
        if (vertex2 == null) {
            vertex2 = new TarjanSCCVertex(data2);
            vertexSet.put(data2, vertex2);
        }
        Label ll = vertex1.nextVertex.put(data2, l);
        return (!l.equals(ll));
    }

    Collection<Collection<TarjanSCCVertex>> sccs = null;

    public Collection<Collection<TarjanSCCVertex>> stronglyConnectedComponents() {
        if (sccs == null) computeSCC();
        return sccs;
    }

    int index;
    Stack<TarjanSCCVertex> sccStack;
    private void computeSCC() {
        index = 0;
        sccs = new ArrayList<>();
        sccStack = new Stack<>();
        for (TarjanSCCVertex v : vertexSet.values()) {
            if (v.index == -1) {
                strongConnect(v);
            }
        }
    }

    private void strongConnect(TarjanSCCVertex v) {
        v.index = index;
        v.lowlink = index;
        index = index + 1;
        v.inStack = true;
        sccStack.push(v);
        for (Data dw : v.nextVertex.keySet()) {
            TarjanSCCVertex w = vertexSet.get(dw);
            if (w.index == -1) {
                strongConnect(w);
                v.lowlink = Math.min(v.lowlink, w.lowlink);
            } else if (w.inStack) {
                v.lowlink = Math.min(v.lowlink, w.index);
            }
        }

        if (v.lowlink == v.index) {
            Collection<TarjanSCCVertex> scc = new HashSet<>();
            TarjanSCCVertex w = null;
            while (w != v) {
                w = sccStack.pop();
                w.inStack = false;
                scc.add(w);
            }
            sccs.add(scc);
        }
    }

    public String getSCCSString() {
        StringBuilder result = new StringBuilder();
        Collection<Collection<TarjanSCCVertex>> sccs = stronglyConnectedComponents();
        for (Collection<TarjanSCCVertex> scc : sccs) {
            result.append("{ ");
            for (TarjanSCCVertex v : scc) {
                result.append(v.toString());
                result.append(" ");
            }
            result.append("}");
            result.append(";\n");
        }
        return result.toString();
    }


    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        for (TarjanSCCVertex vertex : vertexSet.values()) {
            if (vertex.nextVertex.isEmpty()) continue;
            result.append(vertex.toString());
            result.append(" |->");
            for(Map.Entry<Data,Label> next : vertex.nextVertex.entrySet()) {
                result.append(" (");
                result.append(next.getKey().toString());
                result.append(",");
                result.append(next.getValue().toString());
                result.append(") ;");
            }
            result.append("\n");
        }
        return result.toString();
    }
}
