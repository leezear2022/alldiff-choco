/*
 * This file is part of choco-solver, http://choco-solver.org/
 *
 * Copyright (c) 2020, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package org.chocosolver.util.graphOperations.connectivity;

import org.chocosolver.util.objects.IntTuple2;
import org.chocosolver.util.objects.graphs.DirectedGraph;
import org.chocosolver.util.objects.setDataStructures.ISet;

import java.util.*;

public class StrongConnectivityFinder {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************

    // input
    private DirectedGraph graph;
    private BitSet restriction;
    private int n;
    // output
    private int[] sccFirstNode, nextNode, nodeSCC;
    private int nbSCC;

    // util
    private int[] stack, p, inf, nodeOfDfsNum, dfsNumOfNode;
    private Iterator<Integer>[] iterator;
    private BitSet inStack;

    // for early detect
    private Stack<IntTuple2> DE;
    private boolean unconnected = false;

    private ArrayList<IntTuple2> cycles;
    IntTuple2 tt;
    Iterator<IntTuple2> iter;

    //***********************************************************************************
    // CONSTRUCTOR
    //***********************************************************************************

    public StrongConnectivityFinder(DirectedGraph graph) {
        this.graph = graph;
        this.n = graph.getNbMaxNodes();
        //
        stack = new int[n];
        p = new int[n];
        inf = new int[n];
        nodeOfDfsNum = new int[n];
        dfsNumOfNode = new int[n];
        inStack = new BitSet(n);
        restriction = new BitSet(n);
        sccFirstNode = new int[n];
        nextNode = new int[n];
        nodeSCC = new int[n];
        nbSCC = 0;
        //noinspection unchecked
        iterator = new Iterator[n];
        tt = new IntTuple2(-1, -1);
        cycles = new ArrayList<>();
    }

    //***********************************************************************************
    // ALGORITHM
    //***********************************************************************************

    public void findAllSCC() {
        ISet nodes = graph.getNodes();
        for (int i = 0; i < n; i++) {
            restriction.set(i, nodes.contains(i));
        }
        findAllSCCOf(restriction);
    }

    // exception is a set of nodes that do not need to be found SCC
    public void findAllSCC(BitSet exception) {
        ISet nodes = graph.getNodes();
        for (int i = exception.nextClearBit(0); i >= 0 && i < n; i = exception.nextClearBit(i + 1)) {
            restriction.set(i, nodes.contains(i));
        }
        findAllSCCOf(restriction);
    }

    public void findAllSCCOf(BitSet restriction) {
        inStack.clear();
        for (int i = 0; i < n; i++) {
            dfsNumOfNode[i] = 0;
            inf[i] = n + 2;
            nextNode[i] = -1;
            sccFirstNode[i] = -1;
            nodeSCC[i] = -1;
            nodeOfDfsNum[i] = -1;
        }
        nbSCC = 0;
        findSingletons(restriction);
        int first = restriction.nextSetBit(0);
        while (first >= 0) {
            findSCC(first, restriction, stack, p, inf, nodeOfDfsNum, dfsNumOfNode, inStack);
            first = restriction.nextSetBit(first);
        }
    }

    private void findSingletons(BitSet restriction) {
        ISet nodes = graph.getNodes();
        for (int i = restriction.nextSetBit(0); i >= 0; i = restriction.nextSetBit(i + 1)) {
            if (nodes.contains(i) && graph.getPredOf(i).size() * graph.getSuccOf(i).size() == 0) {
                nodeSCC[i] = nbSCC;
                sccFirstNode[nbSCC++] = i;
                restriction.clear(i);
            }
        }
    }

    private void findSCC(int start, BitSet restriction, int[] stack, int[] p, int[] inf, int[] nodeOfDfsNum, int[] dfsNumOfNode, BitSet inStack) {
        int nb = restriction.cardinality();
        // trivial case
        if (nb == 1) {
            nodeSCC[start] = nbSCC;
            sccFirstNode[nbSCC++] = start;
            restriction.clear(start);
            return;
        }
        //initialization
        int stackIdx = 0;
        int k = 0;
        int i = k;
        dfsNumOfNode[start] = k;
        nodeOfDfsNum[k] = start;
        stack[stackIdx++] = i;
        inStack.set(i);
        p[k] = k;
        iterator[k] = graph.getSuccOf(start).iterator();
        int j;
        // algo
        while (true) {
            if (iterator[i].hasNext()) {
                j = iterator[i].next();
                if (restriction.get(j)) {
                    if (dfsNumOfNode[j] == 0 && j != start) {
                        k++;
                        nodeOfDfsNum[k] = j;
                        dfsNumOfNode[j] = k;
                        p[k] = i;
                        i = k;
                        iterator[i] = graph.getSuccOf(j).iterator();
                        stack[stackIdx++] = i;
                        inStack.set(i);
                        inf[i] = i;
                    } else if (inStack.get(dfsNumOfNode[j])) {
                        inf[i] = Math.min(inf[i], dfsNumOfNode[j]);
                    }
                }
            } else {
                if (i == 0) {
                    break;
                }
                if (inf[i] >= i) {
                    int y, z;
                    do {
                        z = stack[--stackIdx];
                        inStack.clear(z);
                        y = nodeOfDfsNum[z];
                        restriction.clear(y);
                        sccAdd(y);
                    } while (z != i);
                    nbSCC++;
                }
                inf[p[i]] = Math.min(inf[p[i]], inf[i]);
                i = p[i];
            }
        }
        if (inStack.cardinality() > 0) {
            int y;
            do {
                y = nodeOfDfsNum[stack[--stackIdx]];
                restriction.clear(y);
                sccAdd(y);
            } while (y != start);
            nbSCC++;
        }
    }

    public boolean findAllSCC_ED(Stack<IntTuple2> deleteEdge) {
        DE = deleteEdge;
        ISet nodes = graph.getNodes();
        for (int i = 0; i < n; i++) {
            restriction.set(i, nodes.contains(i));
        }
        return findAllSCCOf_ED(restriction);
    }


    public boolean findAllSCCOf_ED(BitSet restriction) {
        inStack.clear();
        unconnected = false;
        cycles.clear();
        for (int i = 0; i < n; i++) {
            dfsNumOfNode[i] = 0;
            inf[i] = n + 2;
            nextNode[i] = -1;
            sccFirstNode[i] = -1;
            nodeSCC[i] = -1;
            nodeOfDfsNum[i] = -1;
        }
        nbSCC = 0;
        findSingletons(restriction);
        int first = restriction.nextSetBit(0);
        while (first >= 0) {
            if (findSCC_ED(first, restriction, stack, p, inf, nodeOfDfsNum, dfsNumOfNode, inStack)) {
                return true;
            }
            first = restriction.nextSetBit(first);
        }
        return false;
    }

    private boolean findSCC_ED(int start, BitSet restriction, int[] stack, int[] p, int[] inf, int[] nodeOfDfsNum, int[] dfsNumOfNode, BitSet inStack) {
        int nb = restriction.cardinality();
        // trivial case
        if (nb == 1) {
            nodeSCC[start] = nbSCC;
            sccFirstNode[nbSCC++] = start;
            restriction.clear(start);
            return false;
        }
        //initialization
        int stackIdx = 0;
        int k = 0;
        int i = k;
        dfsNumOfNode[start] = k;
        inf[start] = k;
        nodeOfDfsNum[k] = start;
        stack[stackIdx++] = i;
        inStack.set(i);
        p[k] = k;
        iterator[k] = graph.getSuccOf(start).iterator();
        int j;
        // algo
        while (true) {
            if (iterator[i].hasNext()) {
                j = iterator[i].next();
                if (restriction.get(j)) {
//                    System.out.println(i + ", " + j + ", " + (dfsNumOfNode[j] == 0) + "," + start);
                    if (dfsNumOfNode[j] == 0 && j != start) {
                        k++;
                        nodeOfDfsNum[k] = j;
                        dfsNumOfNode[j] = k;
                        p[k] = i;
                        i = k;
                        iterator[i] = graph.getSuccOf(j).iterator();
                        stack[stackIdx++] = i;
                        inStack.set(i);
                        inf[i] = i;
//                        System.out.println(i + ", " + j + ", " + (dfsNumOfNode[j] == 0) + "," + start);
                    } else if (inStack.get(dfsNumOfNode[j])) {
//                        System.out.println("inf["+i+"]="=inf[i[]);
//                        System.out.println("addc:" + i + "," + j + ", " + inf[j] + ", " + k);
                        inf[i] = Math.min(inf[i], dfsNumOfNode[j]);


//                        System.out.println(Arrays.toString(inf));

                        if (!unconnected) {
                            addCycles(inf[j], k);
                            while (!DE.empty() && inCycles(DE.peek())) {
                                DE.pop();
                            }
                        }

                    }
                }
            } else {
                if (i == 0) {
                    break;
                }
                if (inf[i] >= i) {
                    int y, z;
                    do {
                        z = stack[--stackIdx];
                        inStack.clear(z);
                        y = nodeOfDfsNum[z];
                        restriction.clear(y);
                        sccAdd(y);
                    } while (z != i);
                    nbSCC++;
                    unconnected = true;
                }
                inf[p[i]] = Math.min(inf[p[i]], inf[i]);
                i = p[i];

                if (!unconnected && DE.empty()) {
//                    System.out.println("xixi");
                    return true;
                }
            }
        }
        if (inStack.cardinality() > 0) {
            int y;
            do {
                y = nodeOfDfsNum[stack[--stackIdx]];
                restriction.clear(y);
                sccAdd(y);
            } while (y != start);
            nbSCC++;
        }
        return false;
    }


    private void sccAdd(int y) {
        nodeSCC[y] = nbSCC;
        nextNode[y] = sccFirstNode[nbSCC];
        sccFirstNode[nbSCC] = y;
    }

    //***********************************************************************************
    // ACCESSORS
    //***********************************************************************************

    public int getNbSCC() {
        return nbSCC;
    }

    public int[] getNodesSCC() {
        return nodeSCC;
    }

    public int getSCCFirstNode(int i) {
        return sccFirstNode[i];
    }

    public int getNextNode(int j) {
        return nextNode[j];
    }

    private void addCycles(int a, int b) {

        iter = cycles.iterator();
        while (iter.hasNext()) {
            tt = iter.next();
            if (tt.overlap(a, b)) {
                tt.a = Math.min(tt.a, a);
                tt.b = Math.max(tt.b, b);
                return;
            }
        }

        cycles.add(new IntTuple2(a, b));
    }

    private boolean inCycles(IntTuple2 t) {
//        IntTuple2 tt;
//        System.out.println("inc:" + t.a + "," + t.b + "=" + dfsNumOfNode[t.a] + "," + dfsNumOfNode[t.b]);

        // t.a or t.b is unvisited quit straightly
        if (dfsNumOfNode[t.a] == 0 || dfsNumOfNode[t.b] == 0) {
            return false;
        }
        for (int i = 0, len = cycles.size(); i < len; ++i) {
            tt = cycles.get(i);
            if (tt.cover(dfsNumOfNode[t.a]) && tt.cover(dfsNumOfNode[t.b])) {
                return true;
            }
        }
        return false;
    }

}
