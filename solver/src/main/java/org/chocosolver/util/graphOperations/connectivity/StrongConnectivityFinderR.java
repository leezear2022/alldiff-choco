package org.chocosolver.util.graphOperations.connectivity;

import org.chocosolver.util.objects.IntTuple2;
import org.chocosolver.util.objects.SparseSet;
import org.chocosolver.util.objects.graphs.DirectedGraph;
import org.chocosolver.util.objects.setDataStructures.ISet;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Iterator;
import java.util.Stack;

public class StrongConnectivityFinderR {
    // input
    private DirectedGraph graph;
    private BitSet unvisited;
    private int n;

    //栈
    private int[] stack;
    private BitSet inStack;
    int stackIdx = 0;

    // 标记SCC
    private int nbSCC;
    private int[] nodeSCC;

    //
    private int maxDFS = 1;
    private int[] DFSNum;
    private int[] lowLink;
    private boolean hasSCCSplit = false;
    private Stack<IntTuple2> DE;
    private boolean unconnected = false;

    private ArrayList<IntTuple2> cycles;
    IntTuple2 tt;

    private Iterator<Integer>[] iters;
    private int[] levelNodes;
    private int curLevel = 0;
    private SparseSet singleton;
    private int sccSize = 0;
//    private int index = 0;
//    private BitSet visited;


    public StrongConnectivityFinderR(DirectedGraph graph) {
        this.graph = graph;
        this.n = graph.getNbMaxNodes();

        stack = new int[n];
        inStack = new BitSet(n);

        nodeSCC = new int[n];
        nbSCC = 0;

        DFSNum = new int[n];
        lowLink = new int[n];

        unvisited = new BitSet(n);
        cycles = new ArrayList<>();
        iters = new Iterator[n + 1];
        levelNodes = new int[n + 1];
        singleton = new SparseSet(n);
//        p = new int[n];
//        inf = new int[n];
//        nodeOfDfsNum = new int[n];
//        dfsNumOfNode = new int[n];
//        restriction = new BitSet(n);
//        sccFirstNode = new int[n];
//        nextNode = new int[n];
//        nodeSCC = new int[n];
//        nbSCC = 0;
//        //noinspection unchecked
//        iterator = new Iterator[n];
    }

    public void findAllSCC() {
        singleton.clear();
        ISet nodes = graph.getNodes();
        for (int i = 0; i < n; i++) {
            unvisited.set(i, nodes.contains(i));
        }
        findAllSCCOf(unvisited);
    }

    public void findAllSCC(BitSet exception) {
        singleton.clear();
        ISet nodes = graph.getNodes();
        for (int i = exception.nextClearBit(0); i >= 0 && i < n; i = exception.nextClearBit(i + 1)) {
            unvisited.set(i, nodes.contains(i));
        }
        findAllSCCOf(unvisited);
    }

    private void findAllSCCOf(BitSet restriction) {
        // initialization
        clearStack();
        maxDFS = 0;
        nbSCC = 0;

        for (int i = 0; i < n; i++) {
            lowLink[i] = n + 2;
            nodeSCC[i] = -1;
            DFSNum[i] = n + 2;
        }

        findSingletons(restriction);
        System.out.println("----------");
        System.out.println(restriction);
        int v = restriction.nextSetBit(0);
        while (v >= 0) {
            System.out.println(v);
            strongConnectR(v);
//            strongConnect(v);
            v = restriction.nextSetBit(v);
        }
    }

    private void strongConnectR(int curNode) {
        pushStack(curNode);
        DFSNum[curNode] = maxDFS;
        lowLink[curNode] = maxDFS;
        maxDFS++;
        unvisited.clear(curNode);
//        System.out.println("unvisited clear:" + curNode);

        Iterator<Integer> iterator = graph.getSuccOf(curNode).iterator();
        while (iterator.hasNext()) {
            int newNode = iterator.next();
            System.out.println(curNode + ", " + newNode + ", " + unvisited.get(newNode));
            if (!unvisited.get(newNode)) {
                if (inStack.get(newNode)) {
                    lowLink[curNode] = Math.min(lowLink[curNode], DFSNum[newNode]);
                }
            } else {
                strongConnectR(newNode);
                lowLink[curNode] = Math.min(lowLink[curNode], lowLink[newNode]);
            }
        }

//        System.out.println(curNode + " has no nei " + lowLink[curNode] + ", " + DFSNum[curNode]);
        if (lowLink[curNode] == DFSNum[curNode]) {
            if (lowLink[curNode] > 0 || inStack.cardinality() > 0) {
                hasSCCSplit = true;
            }
            if (hasSCCSplit) {
                System.out.println("scc: " + DFSNum[curNode]);
                int stackNode = -1;
                sccSize = 0;
                while (stackNode != curNode) {
                    stackNode = popStack();
                    System.out.println("pop: " + stackNode + ", " + nbSCC + "," + DFSNum[stackNode]);
                    nodeSCC[stackNode] = nbSCC;
                    sccSize++;
                }
                if (sccSize == 1) {
                    singleton.add(nbSCC);
                }
                nbSCC++;
            }
        }
//        System.out.println("back");
    }

    private void findSingletons(BitSet restriction) {
        ISet nodes = graph.getNodes();
        for (int i = restriction.nextSetBit(0); i >= 0; i = restriction.nextSetBit(i + 1)) {
            if (nodes.contains(i) && graph.getPredOf(i).size() * graph.getSuccOf(i).size() == 0) {
                nodeSCC[i] = nbSCC;
                singleton.add(nbSCC);
                nbSCC++;
                restriction.clear(i);
            }
        }
//        System.out.println("fs: " + Arrays.toString(nodeSCC));
    }

    public boolean findAllSCC_ED(Stack<IntTuple2> deleteEdge) {
        singleton.clear();
        DE = deleteEdge;
        ISet nodes = graph.getNodes();
        for (int i = 0; i < n; i++) {
            unvisited.set(i, nodes.contains(i));
        }
        return findAllSCCOf_ED(unvisited);
    }

    private boolean findAllSCCOf_ED(BitSet restriction) {
        // initialization
        clearStack();
        maxDFS = 0;
        nbSCC = 0;
        unconnected = false;
        cycles.clear();

        for (int i = 0; i < n; i++) {
            lowLink[i] = n + 2;
            nodeSCC[i] = -1;
            DFSNum[i] = -1;
        }

        findSingletons(restriction);
        int v = restriction.nextSetBit(0);
        while (v >= 0) {
//            if (strongConnect_EDR(v)) {
            if (strongConnect_ED(v)) {
                return true;
            }
            v = restriction.nextSetBit(v);
        }
        return false;
    }

    private boolean strongConnect_EDR(int curnode) {
        pushStack(curnode);
        DFSNum[curnode] = maxDFS;
        lowLink[curnode] = maxDFS;
        maxDFS++;
        unvisited.clear(curnode);

        Iterator<Integer> iterator = graph.getSuccOf(curnode).iterator();
        while (iterator.hasNext()) {
            int newNode = iterator.next();
            if (!unvisited.get(newNode)) {
                if (inStack.get(newNode)) {
                    lowLink[curnode] = Math.min(lowLink[curnode], DFSNum[newNode]);
                    if (!unconnected) {
                        addCycles(lowLink[newNode], maxDFS - 1);
                        while (!DE.empty() && inCycles(DE.peek())) {
                            DE.pop();
                        }
                    }
                }
            } else {
                if (strongConnect_EDR(newNode)) {
                    return true;
                }
                lowLink[curnode] = Math.min(lowLink[curnode], lowLink[newNode]);
            }
        }

        if (lowLink[curnode] == DFSNum[curnode]) {
            if (lowLink[curnode] > 0 || inStack.cardinality() > 0) {
                hasSCCSplit = true;
            }
            if (hasSCCSplit) {
                int stackNode = -1;
                sccSize = 0;
                while (stackNode != curnode) {
                    stackNode = popStack();
//                    System.out.println("pop: " + stackNode + ", " + nbSCC);
                    nodeSCC[stackNode] = nbSCC;
                    sccSize++;
                }
                if (sccSize == 1) {
                    singleton.add(nbSCC);
                }
                nbSCC++;

                unconnected = true;
            }
        }

        if (!unconnected && DE.empty()) {
//            System.out.println("xixi");
            return true;
        }

        return false;
    }

    private void strongConnect(int curNode) {
        curLevel = 0;

        pushStack(curNode);
        DFSNum[curNode] = maxDFS;
        lowLink[curNode] = maxDFS;
        maxDFS++;
        unvisited.clear(curNode);
        levelNodes[curLevel] = curNode;
        iters[curLevel] = graph.getSuccOf(curNode).iterator();

        while (stackIdx > 0) {
            curNode = levelNodes[curLevel];
//            System.out.println(curNode + ", " + curLevel);
            if (iters[curLevel].hasNext()) {
                curNode = iters[curLevel].next();
                levelNodes[++curLevel] = curNode;
                System.out.println(levelNodes[curLevel - 1] + ", " + curNode + ", " + unvisited.get(curNode));
                if (unvisited.get(curNode)) {
                    pushStack(curNode);
                    DFSNum[curNode] = maxDFS;
                    lowLink[curNode] = maxDFS;
                    maxDFS++;
                    unvisited.clear(curNode);
                    iters[curLevel] = graph.getSuccOf(curNode).iterator();
                } else if (inStack.get(curNode)) {
                    lowLink[levelNodes[curLevel - 1]] = Math.min(lowLink[levelNodes[curLevel - 1]], DFSNum[curNode]);
                    curLevel--;
//                    System.out.println("back");
                } else {
//                    System.out.println("back");
                    curLevel--;
                }
            } else {
                hasSCCSplit = false;
//                curNode = levelNodes[curLevel - 1];
//                System.out.println(curNode + " has no nei " + lowLink[curNode] + ", " + DFSNum[curNode]);
                if (lowLink[curNode] == DFSNum[curNode]) {
//                    System.out.println(curLevel+", e");
                    if (lowLink[curNode] > 0 || inStack.cardinality() > 0) {
                        hasSCCSplit = true;
                    }
                    if (hasSCCSplit) {
//                        System.out.println(curLevel + ", f");
                        System.out.println("scc: " + DFSNum[curNode]);
                        int stackNode = -1;
                        sccSize = 0;
                        while (stackNode != curNode) {
                            stackNode = popStack();
                            System.out.println("pop: " + stackNode + ", " + nbSCC);
                            nodeSCC[stackNode] = nbSCC;
                            sccSize++;
                        }
                        if (sccSize == 1) {
                            singleton.add(nbSCC);
                        }
                        nbSCC++;
                    }
                }

                if (curLevel == 0) {
                    break;
                }

                lowLink[levelNodes[curLevel - 1]] = Math.min(lowLink[levelNodes[curLevel - 1]], lowLink[curNode]);
                curLevel--;
            }

        }
    }

    private boolean strongConnect_ED(int curNode) {
        curLevel = 0;

        pushStack(curNode);
        DFSNum[curNode] = maxDFS;
        lowLink[curNode] = maxDFS;
        maxDFS++;
        unvisited.clear(curNode);
        levelNodes[curLevel] = curNode;
        iters[curLevel] = graph.getSuccOf(curNode).iterator();

        while (stackIdx > 0) {
            curNode = levelNodes[curLevel];
//            System.out.println(curNode + ", " + curLevel);
            if (iters[curLevel].hasNext()) {
                curNode = iters[curLevel].next();
                levelNodes[++curLevel] = curNode;
//                System.out.println(levelNodes[curLevel - 1] + ", " + curNode + ", " + unvisited.get(curNode));
                if (unvisited.get(curNode)) {
                    pushStack(curNode);
                    DFSNum[curNode] = maxDFS;
                    lowLink[curNode] = maxDFS;
                    maxDFS++;
                    unvisited.clear(curNode);
                    iters[curLevel] = graph.getSuccOf(curNode).iterator();
                } else if (inStack.get(curNode)) {
                    lowLink[levelNodes[curLevel - 1]] = Math.min(lowLink[levelNodes[curLevel - 1]], DFSNum[curNode]);
                    curLevel--;

                    if (!unconnected) {
                        addCycles(lowLink[curNode], maxDFS - 1);
                        while (!DE.empty() && inCycles(DE.peek())) {
                            DE.pop();
                        }
                    }
                } else {
//                    System.out.println("xixi");
                    curLevel--;
                }
            } else {
                hasSCCSplit = false;
//                curNode = levelNodes[curLevel - 1];
//                System.out.println(curNode + " has no nei " + lowLink[curNode] + ", " + DFSNum[curNode]);
                if (lowLink[curNode] == DFSNum[curNode]) {
//                    System.out.println(curLevel+", e");
                    if (lowLink[curNode] > 0 || inStack.cardinality() > 0) {
                        hasSCCSplit = true;
                    }
                    if (hasSCCSplit) {
//                        System.out.println(curLevel + ", f");
                        int stackNode = -1;
                        sccSize = 0;
                        while (stackNode != curNode) {
                            stackNode = popStack();
//                            System.out.println("pop: " + stackNode + ", " + nbSCC);
                            nodeSCC[stackNode] = nbSCC;
                            sccSize++;
                        }
                        if (sccSize == 1) {
                            singleton.add(nbSCC);
                        }
                        nbSCC++;

                        unconnected = true;
                    }
                }

                if (curLevel == 0) {
                    break;
                }

                lowLink[levelNodes[curLevel - 1]] = Math.min(lowLink[levelNodes[curLevel - 1]], lowLink[curNode]);
                curLevel--;

                if (!unconnected && DE.empty()) {
//                    System.out.println("xixi");
                    return true;
                }
            }
        }
        return false;
    }

    private void pushStack(int v) {
        stack[stackIdx++] = v;
        inStack.set(v);
    }

    private void clearStack() {
        inStack.clear();
        stackIdx = 0;
    }

    private int popStack() {
        int x = stack[--stackIdx];
        inStack.clear(x);
        return x;
    }

    public int[] getNodesSCC() {
        return nodeSCC;
    }

    public SparseSet getSingleton() {
        return singleton;
    }

    private void addCycles(int a, int b) {
        Iterator<IntTuple2> iter = cycles.iterator();
        IntTuple2 t;
        while (iter.hasNext()) {
            t = iter.next();
            if (t.overlap(a, b)) {
                t.a = Math.min(t.a, a);
                t.b = Math.max(t.b, b);
                return;
            }
        }

        cycles.add(new IntTuple2(a, b));
    }

    private boolean inCycles(IntTuple2 t) {
        IntTuple2 tt;
        for (int i = 0, len = cycles.size(); i < len; ++i) {
            tt = cycles.get(i);
            if (tt.cover(DFSNum[t.a]) && tt.cover(DFSNum[t.b])) {
                return true;
            }
        }
        return false;
    }
}
