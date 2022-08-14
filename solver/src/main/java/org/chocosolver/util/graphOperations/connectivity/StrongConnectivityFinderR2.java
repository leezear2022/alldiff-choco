package org.chocosolver.util.graphOperations.connectivity;

import gnu.trove.iterator.TIntIterator;
import gnu.trove.iterator.TLongIterator;
import gnu.trove.list.array.TIntArrayList;
import gnu.trove.list.array.TLongArrayList;
import gnu.trove.stack.array.TLongArrayStack;
import org.chocosolver.util.objects.INaiveBitSet;
import org.chocosolver.util.objects.IntPair;
import org.chocosolver.util.objects.RSetPartition;
import org.chocosolver.util.objects.SparseSet;
import org.chocosolver.util.objects.graphs.DirectedGraph;
import org.chocosolver.util.objects.setDataStructures.ISet;

import java.util.*;

public class StrongConnectivityFinderR2 {
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
    private int[] node2SCC;

    //
    private int maxDFS = 1;
    private int[] DFSNum;
    private int[] lowLink;
    private boolean hasSCCSplit = false;
    //    private Stack<IntTuple2> DE;
//    private TIntArrayStack DE;
    private TLongArrayStack DE;
    private boolean unconnected = false;

    //    private ArrayList<IntTuple2> cycles;
    private TLongArrayList cycles;
//    IntTuple2 tt;

    private Iterator<Integer>[] iters;
    private int[] levelNodes;
    private int curLevel = 0;
    private SparseSet singleton;
    private int sccSize = 0;
    private int arity = 0;
    private int addArity = 0;
    private int numValues = 0;
    //    private Iterator<IntTuple2> iter;
    private TLongIterator iter;

    private IntPair nodePair;
    private static int INT_SIZE = 32;

    private RSetPartition partion;

//    private int index = 0;
//    private BitSet visited;


    public StrongConnectivityFinderR2(DirectedGraph graph, int arity, int numValues) {
        this.graph = graph;
        this.n = graph.getNbMaxNodes();

        stack = new int[n];
        inStack = new BitSet(n);

        node2SCC = new int[n];
        nbSCC = 0;

        DFSNum = new int[n];
        lowLink = new int[n];

        unvisited = new BitSet(n);
//        cycles = new ArrayList<>();
        cycles = new TLongArrayList(n);
        iters = new Iterator[n + 1];
        levelNodes = new int[n + 1];
        singleton = new SparseSet(n);
        this.arity = arity;
        this.addArity = arity + 1;
        this.numValues = numValues;
        nodePair = new IntPair(-1, -1);
//        DE = new TIntArrayStack(n);
        DE = new TLongArrayStack(n);
    }

    public StrongConnectivityFinderR2(DirectedGraph graph, int arity, int numValues, RSetPartition p) {
        this.graph = graph;
        this.n = graph.getNbMaxNodes();
        partion = p;

        stack = new int[n];
        inStack = new BitSet(n);

        node2SCC = new int[n];
        nbSCC = 0;

        DFSNum = new int[n];
        lowLink = new int[n];

        unvisited = new BitSet(n);
//        cycles = new ArrayList<>();
        cycles = new TLongArrayList(n);
        iters = new Iterator[n + 1];
        levelNodes = new int[n + 1];
        singleton = new SparseSet(n);
        this.arity = arity;
        this.addArity = arity + 1;
        this.numValues = numValues;
        nodePair = new IntPair(-1, -1);
//        DE = new TIntArrayStack(n);
        DE = new TLongArrayStack(n);
    }

    public void setArity(int arity) {
        this.arity = arity;
        this.addArity = arity + 1;
    }

    public void setUnvisitedValues() {
        ISet nodes = graph.getNodes();
        for (int i = arity; i < n; i++) {
            unvisited.set(i, nodes.contains(i));
        }
    }

    public void findAllSCC() {
        singleton.clear();
        ISet nodes = graph.getNodes();
        for (int i = 0; i < n; i++) {
            unvisited.set(i, nodes.contains(i));
        }
        findAllSCCOf(unvisited);
    }

    public void findAllSCC(int sccIndexStart) {
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

    public boolean findAllSCC(TIntArrayList restriction) {
        singleton.clear();
        ISet nodes = graph.getNodes();
        TIntIterator iter = restriction.iterator();
        while (iter.hasNext()) {
            int i = iter.next();
            unvisited.set(i, nodes.contains(i));
        }
        return findAllSCCOf_ED(unvisited);
    }

    public void findAllSCC(INaiveBitSet vars) {
        singleton.clear();
        ISet nodes = graph.getNodes();
        for (int i = vars.nextClearBit(0); i <= vars.lastSetIndex(); i = vars.nextClearBit(i + 1)) {
            unvisited.set(i, nodes.contains(i));
        }

        findAllSCCOf(unvisited);
    }

    private void findAllSCCOf(BitSet restriction) {
        // initialization
        clearStack();
        maxDFS = 0;
        nbSCC = 0;
        hasSCCSplit = false;
        for (int i = 0; i < n; i++) {
            lowLink[i] = n + 2;
            node2SCC[i] = -1;
            DFSNum[i] = n + 2;
        }

        findSingletons(restriction);
//        System.out.println("----------");
//        System.out.println(restriction);
        int v = restriction.nextSetBit(0);
        while (v >= 0 && v < arity) {
//            System.out.println(v);
//            strongConnectR(v);
            strongConnect(v);
            v = restriction.nextSetBit(v);
        }

//        for (int varIdx = restriction.nextSetBit(0); varIdx < arity; varIdx = restriction.nextSetBit(varIdx + 1)) {
//            strongConnect(varIdx);
//        }
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
//            System.out.println(curNode + ", " + newNode + ", " + unvisited.get(newNode));
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
//                System.out.println("scc: " + DFSNum[curNode]);
                int stackNode = -1;
                sccSize = 0;
                while (stackNode != curNode) {
                    stackNode = popStack();
//                    System.out.println("pop: " + stackNode + ", " + nbSCC + "," + DFSNum[stackNode]);
                    node2SCC[stackNode] = nbSCC;
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
                node2SCC[i] = nbSCC;
                singleton.add(nbSCC);
                nbSCC++;
                restriction.clear(i);
            }
        }
//        System.out.println("fs: " + Arrays.toString(nodeSCC));
    }
//
//    public boolean findAllSCC_ED(TIntArrayStack deleteEdge) {
//        singleton.clear();
//        DE = deleteEdge;
//        ISet nodes = graph.getNodes();
//        for (int i = 0; i < n; i++) {
//            unvisited.set(i, nodes.contains(i));
//        }
//        return findAllSCCOf_ED(unvisited);
//    }


    public boolean findAllSCC_ED(TLongArrayStack deleteEdge) {
        singleton.clear();
        DE = deleteEdge;
        ISet nodes = graph.getNodes();
        for (int i = 0; i < n; i++) {
            unvisited.set(i, nodes.contains(i));
        }
        return findAllSCCOf_ED(unvisited);
    }

    public boolean findAllSCC_ED(TLongArrayStack deleteEdge, TIntArrayList restriction) {
        singleton.clear();
        DE = deleteEdge;
        ISet nodes = graph.getNodes();
        TIntIterator iter = restriction.iterator();

        while (iter.hasNext()) {
            int i = iter.next();
            unvisited.set(i, nodes.contains(i));
        }
//        for (int i = exception.nextClearBit(0); i >= 0 && i < n; i = exception.nextClearBit(i + 1)) {
//            unvisited.set(i, nodes.contains(i));
//        }
        return findAllSCCOf_ED(unvisited);
    }

    private boolean findAllSCCOf_ED(BitSet restriction) {
        // initialization
        clearStack();
        maxDFS = 0;
        nbSCC = 0;
        unconnected = false;
        cycles.clear();
        hasSCCSplit = false;
        for (int i = 0; i < n; i++) {
            lowLink[i] = n + 2;
            node2SCC[i] = -1;
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
                        addCycles(getIntTuple2Long(lowLink[newNode], maxDFS - 1));
                        while (!(DE.size() == 0) && inCycles(DE.peek())) {
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
                    node2SCC[stackNode] = nbSCC;
                    sccSize++;
                }
                if (sccSize == 1) {
                    singleton.add(nbSCC);
                }
                nbSCC++;

                unconnected = true;
            }
        }

        if (!unconnected && (DE.size() == 0)) {
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
//                    System.out.println("back");
                } else {
//                    System.out.println("back");
                    curLevel--;
                }
            } else {
//                hasSCCSplit = false;
//                curNode = levelNodes[curLevel - 1];
//                System.out.println(curNode + " has no nei " + lowLink[curNode] + ", " + DFSNum[curNode]);
                if (lowLink[curNode] == DFSNum[curNode]) {
//                    System.out.println(curLevel+", e");
                    if (lowLink[curNode] > 0 || inStack.cardinality() > 0) {
                        hasSCCSplit = true;
                    }
                    if (hasSCCSplit) {
//                        System.out.println(curLevel + ", f");
//                        System.out.println("scc: " + DFSNum[curNode]);
                        int stackNode = -1;
                        sccSize = 0;
                        while (stackNode != curNode) {
                            stackNode = popStack();
//                            System.out.println("pop: " + stackNode + ", " + nbSCC);
                            node2SCC[stackNode] = nbSCC;
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
        int start = curNode;
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
//                System.out.println(levelNodes[curLevel - 1] + ", " + curNode + ", " + unvisited.get(curNode) + "," + start);
                if (unvisited.get(curNode)) {
                    pushStack(curNode);
                    DFSNum[curNode] = maxDFS;
                    lowLink[curNode] = maxDFS;
                    maxDFS++;
                    unvisited.clear(curNode);
                    iters[curLevel] = graph.getSuccOf(curNode).iterator();
                } else if (inStack.get(curNode)) {
//                    System.out.println("addc:" + levelNodes[curLevel - 1] + ", " + curNode + ", " + lowLink[curNode] + ", " + (maxDFS - 1));
                    lowLink[levelNodes[curLevel - 1]] = Math.min(lowLink[levelNodes[curLevel - 1]], DFSNum[curNode]);
                    curLevel--;


//                    System.out.println(Arrays.toString(lowLink));

                    if (!unconnected) {
                        addCycles(getIntTuple2Long(lowLink[curNode], maxDFS - 1));
                        while (!(DE.size() == 0) && inCycles(DE.peek())) {
                            DE.pop();
                        }
                    }
                } else {
//                    System.out.println("xixi");/**/
                    curLevel--;
                }
            } else {
//                hasSCCSplit = false;
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
                            node2SCC[stackNode] = nbSCC;
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

                if (!unconnected && (DE.size() == 0)) {
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
        return node2SCC;
    }

    public void getNodesSCC(int[] n2c, TIntArrayList[] c2n) {
        for (int i = 0; i < n; i++) {
            int sccIdx = node2SCC[i];
            n2c[i] = sccIdx;
            c2n[sccIdx].add(i);
        }
    }


    public SparseSet getSingleton() {
        return singleton;
    }

    //
//    private void addCycles(int a, int b) {
//        iter = cycles.iterator();
//        while (iter.hasNext()) {
//            tt = iter.next();
//            if (tt.overlap(a, b)) {
//                tt.a = Math.min(tt.a, a);
//                tt.b = Math.max(tt.b, b);
//                return;
//            }
//        }
//
//
////        for (int i = 0, len = cycles.size(); i < len; ++i) {
////            tt = cycles.get(i);
////            if (tt.overlap(a, b)) {
////                tt.a = Math.min(tt.a, a);
////                tt.b = Math.max(tt.b, b);
////                return;
////            }
////        }
//        cycles.add(new IntTuple2(a, b));
//    }

//    private boolean inCycles(IntTuple2 t) {
////        IntTuple2 tt;
////        System.out.println("inc:" + t.a + "," + t.b + "=" + DFSNum[t.a] + "," + DFSNum[t.b]);
//        if (DFSNum[t.a] == -1 || DFSNum[t.b] == -1) {
//            return false;
//        }
//        for (int i = 0, len = cycles.size(); i < len; ++i) {
//            tt = cycles.get(i);
//            if (tt.cover(DFSNum[t.a]) && tt.cover(DFSNum[t.b])) {
//                return true;
//            }
//        }
//
////        iter = cycles.iterator();
////        while (iter.hasNext()) {
////            tt = iter.next();
////            if (tt.cover(DFSNum[t.a]) && tt.cover(DFSNum[t.b])) {
////                return true;
////            }
////        }
//        return false;
//    }

//    private boolean inCycles(long t) {
////        IntTuple2 tt;
////        System.out.println("inc:" + t.a + "," + t.b + "=" + DFSNum[t.a] + "," + DFSNum[t.b]);
//        getIntTuple2(nodePair, t);
//
//        if (DFSNum[nodePair.a] == -1 || DFSNum[nodePair.b] == -1) {
//            return false;
//        }
//
//        for (int i = 0, len = cycles.size(); i < len; ++i) {
//            long tt = cycles.get(i);
//            if (tt.cover(DFSNum[nodePair.a]) && tt.cover(DFSNum[nodePair.b])) {
//                return true;
//            }
//        }
//
//
//        return false;
//    }

//    private boolean inCycles(int vvpIdx) {
//
//        getNodePair(nodePair, vvpIdx);
//
//        if (DFSNum[nodePair.a] == -1 || DFSNum[nodePair.b] == -1) {
//            return false;
//        }
//
//        for (int i = 0, len = cycles.size(); i < len; ++i) {
//            tt = cycles.get(i);
//            if (tt.cover(DFSNum[nodePair.a]) && tt.cover(DFSNum[nodePair.b])) {
//                return true;
//            }
//        }
//
//        return false;
//    }

    private void addCycles(long e) {

        for (int i = 0; i < cycles.size(); i++) {
            long c = cycles.get(i);
            if (overlap(c, e)) {
                cycles.set(i, expand(c, e));
                return;
            }
        }

        cycles.add(e);
    }

    private boolean inCycles(long f) {
//        IntTuple2 tt;
        getIntTuple2(nodePair, f);
//        System.out.println("inc:" + nodePair.a + "," + nodePair.b + "=" + DFSNum[nodePair.a] + "," + DFSNum[nodePair.b);

        if (DFSNum[nodePair.a] == -1 || DFSNum[nodePair.b] == -1) {
            return false;
        }

        for (int i = 0, len = cycles.size(); i < len; ++i) {
            long e = cycles.get(i);
            if (cover(e, DFSNum[nodePair.a], DFSNum[nodePair.b])) {
                return true;
            }
        }


        return false;
    }

    public void getNodePair(IntPair vvp, int vvpIdx) {
        vvp.a = vvpIdx / numValues;
        vvp.b = vvpIdx % numValues + addArity;
    }

    public long getVVPIdx(int x, int a) {
        return x << +a;
    }

    public void getIntTuple2(IntPair vvp, long vvpIdx) {
        vvp.a = (int) (vvpIdx >> INT_SIZE);
        vvp.b = (int) vvpIdx;
    }

    public long getIntTuple2Long(int x, int a) {
        long c = (long) x;
        return c << INT_SIZE | a;
    }

    private boolean overlap(long e, long f) {
        int a = (int) (e >> INT_SIZE);
        int b = (int) e;
        int x = (int) (f >> INT_SIZE);
        int y = (int) f;
//        System.out.println("overlap: " + x + "," + y + "," + a + "," + b);
        return (x >= a && x <= b) || (y >= a && y <= b);
    }

    private boolean cover(long e, long f) {
        int x = (int) (e >> INT_SIZE);
        int y = (int) e;
        int a = (int) (f >> INT_SIZE);
        int b = (int) f;

        return (x >= a && x <= b) && (y >= a && y <= b);
    }

    private boolean cover(long e, int dfsa, int dfsb) {
        int a = (int) (e >> INT_SIZE);
        int b = (int) e;
//        int a = (int) (f >> INT_SIZE);
//        int b = (int) f;

        return (dfsa >= a && dfsa <= b) && (dfsb >= a && dfsb <= b);
    }

    private long expand(long e, long f) {
        int x = (int) (e >> INT_SIZE);
        int y = (int) e;
        int a = (int) (f >> INT_SIZE);
        int b = (int) f;
        return getIntTuple2Long(Math.min(x, a), Math.max(y, b));
    }
}
