/* ==========================================
 * JGraphT : a free Java graph-theory library
 * ==========================================
 *
 * Project Info:  http://jgrapht.sourceforge.net/
 * Project Creator:  Barak Naveh (http://sourceforge.net/users/barak_naveh)
 *
 * (C) Copyright 2003-2008, by Barak Naveh and Contributors.
 *
 * This program and the accompanying materials are dual-licensed under
 * either
 *
 * (a) the terms of the GNU Lesser General Public License version 2.1
 * as published by the Free Software Foundation, or (at your option) any
 * later version.
 *
 * or (per the licensee's choosing)
 *
 * (b) the terms of the Eclipse Public License v1.0 as published by
 * the Eclipse Foundation.
 */
/* -----------------
 * FastLookupDirectedSpecifics.java
 * -----------------
 * (C) Copyright 2015-2015, by Joris Kinable and Contributors.
 *
 * Original Author:  Joris Kinable
 * Contributor(s):
 *
 * $Id$
 *
 * Changes
 * -------
 */
package org.jgrapht.graph.specifics;

import org.jgrapht.Graph;
import org.jgrapht.graph.AbstractBaseGraph;
import org.jgrapht.util.ArrayUnenforcedSet;
import org.jgrapht.util.VertexPair;

import java.io.Serializable;
import java.util.*;

/**
 * Fast implementation of DirectedSpecifics. This class uses additional data structures to improve the performance of methods which depend
 * on edge retrievals, e.g. getEdge(V u, V v), containsEdge(V u, V v),addEdge(V u, V v). A disadvantage is an increase in memory consumption.
 * If memory utilization is an issue, use a {@link DirectedSpecifics} instead.
 *
 * @author Joris Kinable
 */
public class FastLookupDirectedSpecifics_experimental<V,E>
    extends DirectedSpecifics<V,E>
    implements Serializable
{
    private static final long serialVersionUID = 4089085208843722263L;

    /* Maps a pair of vertices <u,v> to an set of edges {(u,v)}. In case of a multigraph, all edges which touch both u,v are included in the set */
    protected Map<ModifiableVertexPair<V>, ArrayUnenforcedSet<E>> touchingVerticesToEdgeMap;
    private ModifiableVertexPair<V> indexPair;

    public FastLookupDirectedSpecifics_experimental(AbstractBaseGraph<V, E> abstractBaseGraph)
    {
        this(abstractBaseGraph, new LinkedHashMap<>());
    }

    public FastLookupDirectedSpecifics_experimental(AbstractBaseGraph<V, E> abstractBaseGraph, Map<V, DirectedEdgeContainer<V, E>> vertexMap)
    {
        super(abstractBaseGraph, vertexMap);
        this.touchingVerticesToEdgeMap=new HashMap<>();
        indexPair=new ModifiableVertexPair<>(null, null);
    }


    /**
     * @see Graph#getAllEdges(Object, Object)
     */
    @Override public synchronized Set<E> getAllEdges(V sourceVertex, V targetVertex)
    {
        if (abstractBaseGraph.containsVertex(sourceVertex)&& abstractBaseGraph.containsVertex(targetVertex)) {
            Set<E> edges = touchingVerticesToEdgeMap.get(indexPair.updatePair(sourceVertex, targetVertex));
            return edges == null ? Collections.emptySet() : new ArrayUnenforcedSet<>(edges);
        }else{
            return null;
        }
    }

    /**
     * @see Graph#getEdge(Object, Object)
     */
    @Override public synchronized E getEdge(V sourceVertex, V targetVertex)
    {
        List<E> edges = touchingVerticesToEdgeMap.get(indexPair.updatePair(sourceVertex, targetVertex));
        if(edges==null || edges.isEmpty())
            return null;
        else
            return edges.get(0);
    }

    @Override public void addEdgeToTouchingVertices(E e)
    {
        V source = abstractBaseGraph.getEdgeSource(e);
        V target = abstractBaseGraph.getEdgeTarget(e);

        getEdgeContainer(source).addOutgoingEdge(e);
        getEdgeContainer(target).addIncomingEdge(e);

        ModifiableVertexPair<V> vertexPair=new ModifiableVertexPair<>(source, target);
        if(!touchingVerticesToEdgeMap.containsKey(vertexPair))
            touchingVerticesToEdgeMap.put(vertexPair, new ArrayUnenforcedSet<>());
        touchingVerticesToEdgeMap.get(vertexPair).add(e);
    }


    @Override public void removeEdgeFromTouchingVertices(E e)
    {
        V source = abstractBaseGraph.getEdgeSource(e);
        V target = abstractBaseGraph.getEdgeTarget(e);

        getEdgeContainer(source).removeOutgoingEdge(e);
        getEdgeContainer(target).removeIncomingEdge(e);

        //Remove the edge from the touchingVerticesToEdgeMap. If there are no more remaining edges for a pair
        //of touching vertices, remove the pair from the map.
        ModifiableVertexPair<V> vertexPair=indexPair.updatePair(source, target);
        if(touchingVerticesToEdgeMap.containsKey(vertexPair)){
            touchingVerticesToEdgeMap.get(vertexPair).remove(e);
            if(touchingVerticesToEdgeMap.get(vertexPair).isEmpty())
                touchingVerticesToEdgeMap.remove(vertexPair);
        }
    }


    public class ModifiableVertexPair<V> extends VertexPair<V>{
        public ModifiableVertexPair(V v1, V v2) {
            super(v1, v2);
        }

        public ModifiableVertexPair updatePair(V v1, V v2){
            this.n1=v1;
            this.n2=v2;
            return this;
        }
    }
}
