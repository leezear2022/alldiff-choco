package org.chocosolver.util.graphOperations.connectivity;

import gnu.trove.iterator.TIntIterator;
import gnu.trove.iterator.TLongIterator;
import gnu.trove.list.array.TIntArrayList;
import gnu.trove.list.array.TLongArrayList;
import gnu.trove.set.hash.TIntHashSet;
import gnu.trove.stack.array.TLongArrayStack;
import org.chocosolver.util.objects.IntTuple2;
import org.chocosolver.util.objects.RSetPartition;
import org.chocosolver.util.objects.SparseSet;
import org.chocosolver.util.objects.graphs.DirectedGraph;
import org.chocosolver.util.objects.setDataStructures.ISet;

import java.util.BitSet;
import java.util.Iterator;

public class StrongConnectivityFinderR3 {
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

    private IntTuple2 nodePair;
    private static int INT_SIZE = 32;

    private RSetPartition partition;
    private int cid;

    public StrongConnectivityFinderR3(DirectedGraph graph, int arity, int numValues) {
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
        nodePair = new IntTuple2(-1, -1);
//        DE = new TIntArrayStack(n);
        DE = new TLongArrayStack(n);

    }

    public StrongConnectivityFinderR3(DirectedGraph graph, int arity, int numValues, RSetPartition p, int cid) {
        this.graph = graph;
        this.n = graph.getNbMaxNodes();
        this.cid = cid;
        partition = p;
        stack = new int[n];
        inStack = new BitSet(n);
        node2SCC = new int[n];
        nbSCC = 0;
        DFSNum = new int[n];
        lowLink = new int[n];
        unvisited = new BitSet(n);
        cycles = new TLongArrayList(n);
        iters = new Iterator[n + 1];
        levelNodes = new int[n + 1];
        singleton = new SparseSet(n);
        this.arity = arity;
        this.addArity = arity + 1;
        this.numValues = numValues;
        nodePair = new IntTuple2(-1, -1);
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
        resetData();
        ISet nodes = graph.getNodes();
        for (int i = 0; i < n; i++) {
//            System.out.println("out: " + i);
            unvisited.set(i, nodes.contains(i));
        }
        findAllSCCOf(unvisited);
    }

    public void findAllSCC(int sccIndexStart) {
        ISet nodes = graph.getNodes();
        partition.setIteratorIndex(sccIndexStart);
        do {
            int ii = partition.getValue();
            unvisited.set(ii, nodes.contains(ii));
        } while (partition.nextValid());
        findAllSCCOf(unvisited);
    }


    public void findAllSCC(BitSet restriction, BitSet unvisited) {
        this.unvisited = unvisited;
//        ISet nodes = graph.getNodes();
//        for (int i = restriction.nextSetBit(0); i >= 0 && i < n; i = restriction.nextSetBit(i + 1)) {
//            unvisited.set(i, nodes.contains(i));
//        }
//        unvisited = restriction;
//        unvisited = restriction;
        findSingletons(unvisited);
//        unvisited = restriction;
//        System.out.println("----------");
//        System.out.println(restriction);
//        resetData();
//        int v = unvisited.nextSetBit(0);
        for (int v = 0; v >= 0 && v < arity; v = unvisited.nextSetBit(v + 1)) {
            strongConnect(v, restriction);
        }
//        while (v >= 0 && v < arity) {
////            System.out.println(v);
////            strongConnectR(v);
//
//            v = unvisited.nextSetBit(v);
//        }

//        findAllSCCOf(unvisited);
    }

//    public boolean findAllSCC(TIntArrayList restriction) {
//        ISet nodes = graph.getNodes();
//        TIntIterator iter = restriction.iterator();
//        while (iter.hasNext()) {
//            int i = iter.next();
//            unvisited.set(i, nodes.contains(i));
//        }
////        resetData();
//        return findAllSCCOf_ED(unvisited);
//    }
//
//    public void findAllSCC(INaiveBitSet vars) {
//        ISet nodes = graph.getNodes();
//        for (int i = vars.nextClearBit(0); i <= vars.lastSetIndex(); i = vars.nextClearBit(i + 1)) {
//            unvisited.set(i, nodes.contains(i));
//        }
//
////        resetData();
//        findAllSCCOf(unvisited);
//    }

    public void resetData() {
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
        singleton.clear();
    }

    public void resetData_ED() {
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
        singleton.clear();
    }

    private void findAllSCCOf(BitSet restriction) {
        findSingletons(restriction);
//        unvisited = restriction;
//        System.out.println("----------");
//        System.out.println(restriction);
        int v = restriction.nextSetBit(0);
        while (v >= 0 && v < arity) {
//            System.out.println(v);
//            strongConnectR(v);
            strongConnect(v, restriction);
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
                    singleton.add(stackNode);
                }
                nbSCC++;
            }
        }
//        System.out.println("back");
    }

    private void findSingletons(BitSet restriction) {
        ISet nodes = graph.getNodes();
        for (int i = restriction.nextSetBit(0); i >= 0; i = restriction.nextSetBit(i + 1)) {
            if (!partition.isSingleton(i) && nodes.contains(i) && graph.getPredOf(i).size() == 0 && graph.getSuccOf(i).size() == 0) {
                node2SCC[i] = nbSCC;
                singleton.add(i);
//                System.out.println("singleton add: " + i + ", " + partition);
                partition.remove(i);
                restriction.clear(i);
                nbSCC++;
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
        DE = deleteEdge;
        ISet nodes = graph.getNodes();
        for (int i = 0; i < n; i++) {
            unvisited.set(i, nodes.contains(i));
        }
        return findAllSCCOf_ED(unvisited);
    }

    public boolean findAllSCC_ED(int sccIndexStart, TLongArrayStack deleteEdge) {
        DE = deleteEdge;
        ISet nodes = graph.getNodes();
        partition.setIteratorIndex(sccIndexStart);
        do {
            int ii = partition.getValue();
            unvisited.set(ii, nodes.contains(ii));
        } while (partition.nextValid());
        return findAllSCCOf_ED(unvisited);
    }


    public boolean findAllSCC_ED(TLongArrayStack deleteEdge, TIntArrayList restriction) {
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
        findSingletons(restriction);
//        cycles.clear();
//        unconnected = false;
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
                    singleton.add(stackNode);
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

    private void strongConnect(int curNode, BitSet restriction) {
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
//            if (cid == 12 && curLevel == 2 && curNode == 2) {
////                System.out.println("xixi:" + graph.getSuccOf(curNode));
//            }
            if (iters[curLevel].hasNext()) {
                curNode = iters[curLevel].next();
                //在本partition的限定范围内
                if (restriction.get(curNode)) {
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
                }
            } else {
//                hasSCCSplit = false;
//                curNode = levelNodes[curLevel - 1];
//                if (cid == 30)
//                    System.out.println(curNode + " has no nei " + lowLink[curNode] + ", " + DFSNum[curNode]);
                if (lowLink[curNode] == DFSNum[curNode]) {
//                    if (cid == 30)
//                        System.out.println(curLevel + ", e");
                    if (lowLink[curNode] > 0 || inStack.cardinality() > 0) {
                        hasSCCSplit = true;
                    }
                    if (hasSCCSplit) {
//                        if (cid == 30) {
//                            System.out.println(curLevel + ", f");
//                            System.out.println("scc: " + DFSNum[curNode]);
//                        }
                        int stackNode = -1;
                        sccSize = 0;
//                        System.out.println("before set limit: " + partition);
                        int limit = partition.resetLimitByElement(curNode);
//                        System.out.println("set limit: " + limit + ", curNode: " + curNode + ", " + partition);
                        while (stackNode != curNode) {
                            stackNode = popStack();
//                            if (cid == 30)
//                                System.out.println("pop: " + stackNode + ", " + nbSCC);

                            partition.add(stackNode);
                            node2SCC[stackNode] = nbSCC;
                            sccSize++;
                        }
                        if (sccSize == 1) {
                            singleton.add(stackNode);
                        }
                        partition.setSplit();
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
//                        System.out.println("before set limit: " + partition);
                        int limit = partition.resetLimitByElement(curNode);
//                        System.out.println("set limit: " + limit + ", curNode: " + curNode + ", " + partition);
                        while (stackNode != curNode) {
                            stackNode = popStack();
//                            System.out.println("pop: " + stackNode + ", " + nbSCC);
                            partition.add(stackNode);
                            node2SCC[stackNode] = nbSCC;
                            sccSize++;
                        }
                        if (sccSize == 1) {
                            singleton.add(stackNode);
                        }
                        partition.setSplit();
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

    public void getNodePair(IntTuple2 vvp, int vvpIdx) {
        vvp.a = vvpIdx / numValues;
        vvp.b = vvpIdx % numValues + addArity;
    }

    public long getVVPIdx(int x, int a) {
        return x << +a;
    }

    public void getIntTuple2(IntTuple2 vvp, long vvpIdx) {
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


    public IntTuple2 getIntTuple2(long vvpIdx) {
        return new IntTuple2((int) (vvpIdx >> INT_SIZE), (int) vvpIdx);
    }


    public void getAllSCCStartIndices(TIntHashSet sccStartIndex) {
        partition.getSCCStartIndex(sccStartIndex);
    }
}
