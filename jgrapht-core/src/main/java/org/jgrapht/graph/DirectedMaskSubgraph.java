/*
 * (C) Copyright 2007-2017, by France Telecom and Contributors.
 *
 * JGraphT : a free Java graph-theory library
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
package org.jgrapht.graph;

import java.util.function.*;

import org.jgrapht.*;

/**
 * A directed graph that is a {@link MaskSubgraph} of another graph.
 *
 * @param <V> the graph vertex type
 * @param <E> the graph edge type
 *
 * @author Guillaume Boulmier
 * @since July 5, 2007
 * @deprecated In favor of {@link MaskSubgraph}.
 */
@Deprecated
public class DirectedMaskSubgraph<V, E>
    extends MaskSubgraph<V, E>
    implements DirectedGraph<V, E>
{

    /**
     * Create a new directed {@link MaskSubgraph} of another graph.
     *
     * @param base the base graph
     * @param vertexMask vertices to exclude in the subgraph. If a vertex is masked, it is as if it
     *        is not in the subgraph. Edges incident to the masked vertex are also masked.
     * @param edgeMask edges to exclude in the subgraph. If an edge is masked, it is as if it is not
     *        in the subgraph.
     */
    public DirectedMaskSubgraph(
        DirectedGraph<V, E> base, Predicate<V> vertexMask, Predicate<E> edgeMask)
    {
        super(base, vertexMask, edgeMask);
    }
}

// End DirectedMaskSubgraph.java
