/*
 * (C) Copyright 2017-2017, by Joris Kinable and Contributors.
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

package org.jgrapht.alg.cycle;

import org.jgrapht.Graph;
import org.jgrapht.GraphPath;
import org.jgrapht.GraphTests;
import org.jgrapht.Graphs;
import org.jgrapht.alg.cycle.HierholzerEulerianCycle;
import org.jgrapht.alg.interfaces.EulerianCycleAlgorithm;
import org.jgrapht.alg.interfaces.ShortestPathAlgorithm;
import org.jgrapht.alg.shortestpath.DijkstraShortestPath;
import org.jgrapht.alg.util.Pair;
import org.jgrapht.alg.util.UnorderedPair;
import org.jgrapht.graph.*;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * This class solves the Chinese Postman Problem (CPP), also known as the Route Inspection Problem.
 * The CPP asks to find a shortest closed path or circuit that visits every edge of a graph. In
 * weighted graphs, the circuit of minimal total weight is returned; in unweighted graphs, a circuit
 * of minimum total length (total number of edges) is returned.
 * <p>
 * The algorithm works with undirected graphs which may contain loops and/or multiple
 * edges. The runtime complexity is O(N^3) where N is the number of vertices in the graph. Mixed
 * graphs are currently not supported, as solving the CPP for mixed graphs is NP-hard. The graph on
 * which this algorithm is invoked must be strongly connected; invoking this algorithm on a graph
 * which is not strongly connected may result in undefined behavior. In case of weighted graphs, all
 * edge weights must be positive.
 *
 * If the input graph is Eulerian (see {@link GraphTests#isEulerian(Graph)} for details) use
 * {@link HierholzerEulerianCycle} instead.
 * <p>
 * The implementation is based on the following paper:<br>
 * Edmonds, J., Johnson, E.L. Matching, Euler tours and the Chinese postman, Mathematical
 * Programming (1973) 5: 88. doi:10.1007/BF01580113<br>
 *
 * More concise descriptions of the algorithms can be found here:
 * <ul>
 * <li><a href=
 * "http://www.suffolkmaths.co.uk/pages/Maths%20Projects/Projects/Topology%20and%20Graph%20Theory/Chinese%20Postman%20Problem.pdf">CPP
 * for Undirected graphs</a>
 * <li><a href=
 * "https://www-m9.ma.tum.de/graph-algorithms/directed-chinese-postman/index_en.html">CPP for
 * Directed graphs</a>
 * </ul>
 * 
 * @param <V> the graph vertex type
 * @param <E> the graph edge type
 *
 * @author Joris Kinable
 * @since March 2017
 */
public class UndirectedChinesePostman<V, E>
{
    private void findPairs(Set<V> set,
            List<UnorderedPair<V, V>> currentResults,
            List<List<UnorderedPair<V, V>>> results)
    {
        if (set.size() < 2)
        {
            results.add(new ArrayList<UnorderedPair<V, V>>(currentResults));
            return;
        }
        List<V> list = new ArrayList<V>(set);
        V first = list.remove(0);
        for (int i=0; i<list.size(); i++)
        {
            V second = list.get(i);
            Set<V> nextSet = new LinkedHashSet<V>(list);
            nextSet.remove(second);

            UnorderedPair<V, V> pair = new UnorderedPair<>(first, second);
            currentResults.add(pair);
            findPairs(nextSet, currentResults, results);
            currentResults.remove(pair);
        }
    }

    private List<UnorderedPair<V,V>> findPairsBruteForce(Set<V> set,
            final Map<UnorderedPair<V, V>, GraphPath<V, E>> shortestPaths)
    {
        List<UnorderedPair<V,V>> res = null;
        ArrayList<List<UnorderedPair<V, V>>> pairlists = new ArrayList<>();
        findPairs(set, new ArrayList<UnorderedPair<V, V>>(), pairlists);


        double weight = -1;
        for (List<UnorderedPair<V, V>> pairlist : pairlists)
        {
            double possibleWeight = 0;
            for (UnorderedPair<V, V> pair : pairlist)
            {
                possibleWeight += shortestPaths.get(pair).getWeight();
            }
            if (weight == -1 || possibleWeight < weight)
            {
                weight = possibleWeight;
                res = pairlist;
            }
        }
        return res;
    }

    private List<UnorderedPair<V,V>> findPairsHeuristic(Set<V> set,
            final Map<UnorderedPair<V, V>, GraphPath<V, E>> shortestPaths)
    {
        TreeSet<UnorderedPair<V,V>> pairs = new TreeSet<>(new Comparator<UnorderedPair<V,V>>()
                {
                    public int compare(UnorderedPair<V,V> a, UnorderedPair<V,V> b)
                    {
                        return (int) Math.signum(shortestPaths.get(a).getWeight() - shortestPaths.get(b).getWeight());
                    }
                }
                );
        pairs.addAll(shortestPaths.keySet());
        List<UnorderedPair<V,V>> res = new ArrayList<>();
        while(!pairs.isEmpty())
        {
            UnorderedPair<V,V> picked = pairs.first();
            res.add(picked);
            List<UnorderedPair<V,V>> toRemove = new ArrayList<>();
            for (UnorderedPair<V,V> p : pairs)
            {
                if (p.getFirst().equals(picked.getFirst()) || p.getSecond().equals(picked.getFirst())
                        ||p.getFirst().equals(picked.getSecond()) || p.getSecond().equals(picked.getSecond()))
                {
                    toRemove.add(p);
                }
            }
            for (UnorderedPair<V,V> p : toRemove)
            {
                pairs.remove(p);
            }
        }
        return res;
    }

    /**
     * Solves the CPP for undirected graphs
     *
     * @param graph input graph
     * @return Eulerian Circuit
     */
    public GraphPath<V, E> solveCPPUndirected(Graph<V, E> graph)
    {
        // 1. Find all odd degree vertices (there should be an odd number of those)
        List<V> oddDegreeVertices =
        graph.vertexSet().stream().filter(v -> graph.degreeOf(v) % 2 == 1).collect(
                Collectors.toList());

        // 2. Compute all pairwise shortest paths for the oddDegreeVertices
        Map<UnorderedPair<V, V>, GraphPath<V, E>> shortestPaths = new HashMap<>();
        ShortestPathAlgorithm<V, E> sp = new DijkstraShortestPath<>(graph);
        for (int i = 0; i < oddDegreeVertices.size() - 1; i++) {
            for (int j = i + 1; j < oddDegreeVertices.size(); j++) {
                V u = oddDegreeVertices.get(i);
                V v = oddDegreeVertices.get(j);
                shortestPaths.put(new UnorderedPair<>(u, v), sp.getPath(u, v));
            }
        }

        // 3. Solve a matching problem. For that we create an auxiliary graph.
        Set<V> set = new LinkedHashSet<V>(oddDegreeVertices);

        List<UnorderedPair<V, V>> chosen = null;
        if (set.size() > 0)
        {
            chosen = findPairsHeuristic(set, shortestPaths);
        }
        else
        {
            chosen = findPairsBruteForce(set, shortestPaths);
        }

        Graph<Integer, DefaultWeightedEdge> auxGraph =
        new SimpleWeightedGraph<>(DefaultWeightedEdge.class);

        // 4. On the original graph, add shortcuts between the odd vertices. These shortcuts have
        // been identified by the matching algorithm. A shortcut from u to v
        // indirectly implies duplicating all edges on the shortest path from u to v

        Graph<V, E> eulerGraph = new Pseudograph<>(graph.getEdgeFactory());
        Graphs.addAllVertices(eulerGraph, graph.vertexSet());
        Graphs.addAllEdges(eulerGraph, graph, graph.edgeSet());
        Map<E, GraphPath<V, E>> shortcutEdges = new HashMap<>();

        for (UnorderedPair<V, V> pair : chosen) {
            GraphPath<V,E> path = shortestPaths.get(pair);
            V u = pair.getFirst();
            V v = pair.getSecond();
            E shortcutEdge = eulerGraph.addEdge(u, v);
            shortcutEdges.put(shortcutEdge, path);
        }

        EulerianCycleAlgorithm<V, E> eulerianCycleAlgorithm = new HierholzerEulerianCycle<>();
        GraphPath<V, E> pathWithShortcuts = eulerianCycleAlgorithm.getEulerianCycle(eulerGraph);
        return replaceShortcutEdges(graph, pathWithShortcuts, shortcutEdges);
    }

    private GraphPath<V, E> replaceShortcutEdges(
            Graph<V, E> inputGraph, GraphPath<V, E> pathWithShortcuts,
            Map<E, GraphPath<V, E>> shortcutEdges)
    {
        V startVertex = pathWithShortcuts.getStartVertex();
        V endVertex = pathWithShortcuts.getEndVertex();
        List<V> vertexList = new ArrayList<>();
        List<E> edgeList = new ArrayList<>();

        List<V> verticesInPathWithShortcuts = pathWithShortcuts.getVertexList(); // should contain
        // at least 2
        // vertices
        List<E> edgesInPathWithShortcuts = pathWithShortcuts.getEdgeList(); // cannot be empty
        for (int i = 0; i < verticesInPathWithShortcuts.size() - 1; i++) {
            vertexList.add(verticesInPathWithShortcuts.get(i));
            E edge = edgesInPathWithShortcuts.get(i);

            if (shortcutEdges.containsKey(edge)) { // shortcut edge
                // replace shortcut edge by its implied path
                GraphPath<V, E> shortcut = shortcutEdges.get(edge);
                if (vertexList.get(vertexList.size() - 1).equals(shortcut.getStartVertex())) { // check
                    // direction
                    // of
                    // path
                    vertexList.addAll(
                            shortcut.getVertexList().subList(1, shortcut.getVertexList().size() - 1));
                    edgeList.addAll(shortcut.getEdgeList());
                } else {
                    List<V> reverseVertices = new ArrayList<>(
                            shortcut.getVertexList().subList(1, shortcut.getVertexList().size() - 1));
                    Collections.reverse(reverseVertices);
                    List<E> reverseEdges = new ArrayList<>(shortcut.getEdgeList());
                    Collections.reverse(reverseEdges);
                    vertexList.addAll(reverseVertices);
                    edgeList.addAll(reverseEdges);
                }
            } else { // original edge
                edgeList.add(edge);
            }
        }
        vertexList.add(endVertex);
        double pathWeight = edgeList.stream().mapToDouble(inputGraph::getEdgeWeight).sum();

        return new GraphWalk<>(
                inputGraph, startVertex, endVertex, vertexList, edgeList, pathWeight);
    }
}
