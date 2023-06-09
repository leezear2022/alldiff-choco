//package org.chocosolver.solver.constraints.nary.alldifferent.algo;
//
////import org.chocosolver.amtf.Measurer;
//
//import gnu.trove.list.array.TIntArrayList;
//import org.chocosolver.memory.IStateBitSet;
//import org.chocosolver.memory.IStateInt;
//import org.chocosolver.solver.ICause;
//import org.chocosolver.solver.Model;
//import org.chocosolver.solver.exception.ContradictionException;
//import org.chocosolver.solver.variables.IntVar;
//import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
//import org.chocosolver.util.iterators.DisposableValueIterator;
//import org.chocosolver.util.objects.*;
//import org.chocosolver.util.procedure.UnaryIntProcedure;
//
//import java.util.BitSet;
//
///**
// * Algorithm of Alldifferent with AC
// * <p>
// * Uses Zhang algorithm in the paper of IJCAI-18
// * "A Fast Algorithm for Generalized Arc Consistency of the Alldifferent Constraint"
// * <p>
// * We try to use the bit to speed up.
// * <p>
// * <p>
// *
// * @author Jean-Guillaume Fages, Zhe Li, Jia'nan Chen
// */
//public class AlgoAllDiffAC_WordRamWordRamBak3 extends AlgoAllDiffAC_Simple {
//    private final SimpleBitSet varsMask;
//
//
//    //***********************************************************************************
//    // VARIABLES
//    //***********************************************************************************
//
//    // matching
//    private IStateInt[] val2VarR;
//    private IStateInt[] var2ValR;
//    // 记录队列
//    private int[] visiting_;
//    private int[] variable_visited_from_;
//
//    // 变量到变量的连通性
//    // 对于惰性算法，记录是否知道-变量到变量的连通性
////    private SimpleBitSet[] graphLinkedMatrix;
////    private SimpleBitSet[] graphLinkedFrontier;
//
//    // !! 记录gamma的前沿
////    private SimpleBitSet gammaFrontier;
//    // 记录gamma的bitset
////    private SimpleBitSet gammaMask;
//
//    // 记录scc
//    protected boolean initialPropagation = true;
//    protected IStatePartition partition;
//    private SparseSet triggeringVars;
//    //    private SparseSet triggeringVals;
//    private final IIntDeltaMonitor[] monitors;
//    private final UnaryIntProcedure<Integer> onValRem;
//    //    private SparseSet[] deletedValues;
//    protected SparseSet varsTmp;
//    private SparseSet changedSCCStartIndex;
////    protected boolean unconnected = false;
////    protected boolean isSkiped = false;
//
//    long startTime;
//
//    IStateBitSet[] RB;
//    IStateBitSet[] RD;
//    // if all a in var x val2Idx[a] = a then DomIsRagular[x] = true
//    boolean[] domIsRegular;
//
//    // for Zhang18
//    private IStateBitSet matchedValuesR;
//    private IStateBitSet validValuesR;
//    //    private SimpleBitSet A;
//    private final IStateBitSet freeNodesR;
//
//    // for early detect
//    private TIntArrayList sccTriggeringVars;
////    private int numSCCDeleteValues;
////    private int numSCCValues;
//
//    private IStateBitSet activeVars;
//
//    //栈
//    protected int[] varStack;
//    protected int[] valStack;
//    protected SimpleBitSet varIsInStack;
//    protected SimpleBitSet valIsInStack;
//    int varStackIdx;
//    int valStackIdx;
//
//    protected int maxDFS = 0;
//    protected int[] varDFSNum;
//    protected int[] valDFSNum;
//    protected int[] varLowLink;
//    protected int[] valLowLink;
//    protected boolean hasSCCSplit = false;
//
//    int sinkDFSNum;
//    int sinkLowLink;
//    boolean sinkIsInStack;
//    protected boolean sinkIsUnvisited;
//
//    protected int endBitIndex = 64;
//    private final SimpleBitSet needVisitValues;
//    private SparseSet valsTmp;
//
//    private SimpleBitSet unVisitedValues;
//    // 已访问过的变量和值
//    private SimpleBitSet unVisitedVariables;
//    private BitSet visitedValues;
//
//    private SimpleBitSet valsMask;
//
//    //***********************************************************************************
//    // CONSTRUCTORS
//    //***********************************************************************************
//    public AlgoAllDiffAC_WordRamWordRamBak3(IntVar[] variables, ICause cause, Model model) {
//        super(variables, cause, model.getEnvironment());
//        id = num++;
////        System.out.println("id: " + id + " Zhang1820");
//        RB = new IStateBitSet[numValues];
//        for (int i = 0; i < numValues; ++i) {
//            RB[i] = env.makeBitSet(arity);
//        }
//
//        RD = new IStateBitSet[arity];
//        domIsRegular = new boolean[arity];
//        for (int i = 0; i < arity; i++) {
//            RD[i] = env.makeBitSet(numValues);
//        }
//
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            DisposableValueIterator vit = v.getValueIterator(true);
//            domIsRegular[i] = true;
//            while (vit.hasNext()) {
//                int val = vit.next();
//                int valIdx = val2Idx.get(val);
//                if (domIsRegular[i] && val != valIdx)
//                    domIsRegular[i] = false;
//                RB[valIdx].set(i);
//                RD[i].set(valIdx);
//            }
//            vit.dispose();
//        }
//
//        // 记录访问过的变量
//        visiting_ = new int[arity];
//        unVisitedVariables = new SimpleBitSet(arity);
//        unVisitedValues = new SimpleBitSet(numValues);
//        // 变量的前驱变量，若前驱变量是-1，则表示无前驱变量，就是第一个变量
//        variable_visited_from_ = new int[arity];
//        visitedValues = new BitSet(numValues);
//        matchedValuesR = env.makeBitSet(numValues);
//        validValuesR = env.makeBitSet(numValues);
////        A = new SimpleBitSet(numValues);
////        fn = new SimpleBitSet(numValues);
//        freeNodesR = env.makeBitSet(numValues);
//
//        for (int i = 0; i < numValues; i++) {
//            validValuesR.set(i);
//            freeNodesR.set(i);
//        }
//
//        var2ValR = new IStateInt[arity];
//        val2VarR = new IStateInt[numValues];
//
//        for (int i = 0; i < arity; ++i) {
//            var2ValR[i] = env.makeInt(-1);
//        }
//        for (int i = 0; i < numValues; ++i) {
//            val2VarR[i] = env.makeInt(-1);
//        }
//
////        gammaFrontier = new SimpleBitSet(arity);
////        gammaMask = new SimpleBitSet(arity);
////
////        graphLinkedMatrix = new SimpleBitSet[arity];
////        graphLinkedFrontier = new SimpleBitSet[arity];
////        for (int i = 0; i < arity; ++i) {
////            graphLinkedMatrix[i] = new SimpleBitSet(arity);
////            graphLinkedFrontier[i] = new SimpleBitSet(arity);
////        }
//
//        // for Gent algorithm
//        partition = makePartition(arity, env);
//        triggeringVars = new SparseSet(arity);
//        // 已懒更新的变量/值
//        varsTmp = new SparseSet(arity);
//        valsTmp = new SparseSet(numValues);
//
//        changedSCCStartIndex = new SparseSet(arity);
//        monitors = new IIntDeltaMonitor[vars.length];
//        for (int i = 0; i < vars.length; i++) {
//            monitors[i] = vars[i].monitorDelta(cause);
//        }
//        onValRem = makeProcedure();
//
////        deletedValues = new SparseSet[arity];
////        for (int i = 0; i < arity; i++) {
////            deletedValues[i] = new SparseSet(numValues);
////        }
//
//        sccTriggeringVars = new TIntArrayList(arity);
//        activeVars = env.makeBitSet(arity);
//        activeVars.set(0, arity);
//
//        varStack = new int[arity];
//        valStack = new int[numValues];
//
//        varIsInStack = new SimpleBitSet(arity);
//        valIsInStack = new SimpleBitSet(numValues);
//
//        varDFSNum = new int[arity];
//        valDFSNum = new int[numValues];
//        varLowLink = new int[arity];
//        valLowLink = new int[numValues];
//        needVisitValues = new SimpleBitSet(numValues);
//        valsMask = new SimpleBitSet(numValues);
//        varsMask = new SimpleBitSet(arity);
//    }
//
//    protected UnaryIntProcedure<Integer> makeProcedure() {
//        return new UnaryIntProcedure<Integer>() {
//            int varIdx;
//            IntVar v;
//            int matchedVal = -1;
//            boolean isReg;
//
//            @Override
//            public UnaryIntProcedure set(Integer o) {
//                varIdx = o;
//                v = vars[varIdx];
//                matchedVal = var2ValR[varIdx].get();
//                isReg = domIsRegular[varIdx];
//                return this;
//            }
//
//            @Override
//            public void execute(int i) {
//                int valIdx = isReg ? i : val2Idx.get(i);
//
//                // 删的值是匹配值，清理匹配
//                if (valIdx == matchedVal) {
//                    var2ValR[varIdx].set(-1);
//                    val2VarR[valIdx].set(-1);
//                    matchedValuesR.clear(valIdx);
//                    freeNodesR.set(valIdx);
//                }
//
//                removeValueR(varIdx, valIdx);
//
//                // bel删空表示该值失效
//                if (RB[valIdx].isEmpty()) {
//                    validValuesR.clear(valIdx);
//                    freeNodesR.clear(valIdx);
//                }
//
////                System.out.println("delta: " + varIdx + ", " + valIdx);
//            }
//        };
//    }
//
//
//    //***********************************************************************************
//    // PROPAGATION
//    //***********************************************************************************
//
//    public boolean propagate() throws ContradictionException {
////        System.out.println(" propagate: " + (++numCall) + "----------------");
//        ++numCall;
//        System.out.println("----------------" + id + " propagate: " + numCall + "----------------");
//        printDomains();
//
//        boolean filter = false;
//        Measurer.enterProp();
//        if (initialPropagation) {
////            triggeringVals.fill();
////            triggeringVars.fill();
////            updatedVars.fill();
////            updatedVals.fill();
//            startTime = System.nanoTime();
//            deltaUpdate();
//            findMaximumMatching();
//            Measurer.matchingTime += System.nanoTime() - startTime;
//            startTime = System.nanoTime();
//
//            resetData(varsTmp, valsTmp, true);
//            findAllSCC(restriction, varsTmp);
////            A.setNegAnd(matchedValuesR, validValuesR);
////            System.out.println("freeNodes:\t" + A);
////            System.out.println("freeNodesR:\t" + freeNodesR);
////            if (!A.eq(freeNodesR)) {
////                System.out.println("free nodes error!!");
////            }
//            // for Zhang18
//            // 有freeNodes才执行。在gamma区中过滤
//            if (freeNodesR.isEmpty()) {
//                initiateMatrixOrdinary(0);
//                filter |= filterDomainsPartition(0);
//            } else {
//                int newSCCStart = distinguish();
////                System.out.println("gamma: " + gammaMask);
//                if (newSCCStart != -1) {
//                    filter |= filterDomainsGamma();
//                    // gamma分裂区中建图过滤
//                    initiateMatrixAfterGamma(newSCCStart);
////                    filter |= filterDomainsAfterGamma(newSCCStart);
//                    filter |= filterDomainsPartition(newSCCStart);
//                }
//            }
//            Measurer.filterTime += System.nanoTime() - startTime;
////            System.out.println(partition);
//            initialPropagation = false;
//        } else {
//            startTime = System.nanoTime();
//            deltaUpdate();
////            checkDomains();
//            filter |= propagate_SCC_Match();
////            if (numCall == 694)
////                System.out.println("matching: " + Arrays.toString(var2ValR));
//            Measurer.matchingTime += System.nanoTime() - startTime;
//            startTime = System.nanoTime();
//            filter |= propagate_SCC_filter();
//            Measurer.filterTime += System.nanoTime() - startTime;
//        }
////        dealChanges();
////        checkDomains();
////        if (numCall == 683) {
////            printDomains();
////        }
////        System.out.println(partition);
////        if (numCall <= 696 && numCall >= 693) {
////            System.out.println("----after----");
////            printDomains();
////        }
//        return filter;
//    }
//
//    //***********************************************************************************
//    // Initialization
//    //***********************************************************************************
//
//    private void printDomains() {
//        // 填充B和D
//        System.out.println("****doms*****");
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            System.out.println(v);
//        }
//        System.out.println("*************");
////        // 填充B和D
////        for (int i = 0; i < arity; ++i) {
////            IntVar v = vars[i];
////            System.out.println(RD[i]);
////        }
//    }
//
//    private void printDomains(int varIdx) {
//        // 填充B和D
//        System.out.println("****var:" + varIdx + "*****");
//        IntVar v = vars[varIdx];
//        System.out.printf("v:%d = %s, size = %d\n", varIdx, v, v.getDomainSize());
//        System.out.printf("v:%d = %s, size = %d\n", varIdx, RD[varIdx], RD[varIdx].cardinality());
//        System.out.println("*************");
////        // 填充B和D
////        for (int i = 0; i < arity; ++i) {
////            IntVar v = vars[i];
////            System.out.println(RD[i]);
////        }
//    }
//
//    private boolean checkDomains() {
//        // 填充B和D
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            boolean isRegular = domIsRegular[i];
//            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
//                int k = isRegular ? j : val2Idx.get(j);
//                if (!RD[i].get(k)) {
//                    System.out.printf("error0 @%d: (%d, %d)\n", numCall, i, k);
//                    return false;
//                }
//                if (!RB[k].get(i)) {
//                    System.out.printf("error1 @%d: (%d, %d)\n", numCall, i, k);
//                    return false;
//                }
//            }
//
//            for (int j = RD[i].nextSetBit(0); j >= 0; j = RD[i].nextSetBit(j + 1)) {
//                int k = idx2Val[j];
//                if (!v.contains(k)) {
//                    System.out.printf("error2 @%d: (%d, %d)\n", numCall, i, k);
//                }
//            }
//
//        }
//
//
//        for (int i = 0; i < numValues; i++) {
//            for (int j = RB[i].nextSetBit(0); j >= 0; j = RB[i].nextSetBit(j + 1)) {
//                IntVar v = vars[j];
//                int k = idx2Val[i];
//                if (!v.contains(k)) {
//                    System.out.printf("error3 @%d: (%d, %d)\n", numCall, i, k);
//                    System.out.println(v);
//                    System.out.println(RB[i]);
//                    for (int l = RB[i].nextSetBit(0); l >= 0; l = RB[i].nextSetBit(l + 1)) {
//                        IntVar vv = vars[l];
//                        System.out.print("contain: ");
//                        if (vv.contains(k)) {
//                            System.out.print(l + " ");
//                        }
//                        System.out.println();
//                    }
//                    System.exit(0);
//                    return false;
//                }
//            }
//        }
//
//        return true;
//    }
//
//    private void deltaUpdate() throws ContradictionException {
//        // 触发队列和更新队列
//        triggeringVars.clear();
////        updatedVars.clear();
////        updatedVals.clear();
//
////        for (int varIdx = 0; varIdx < arity; varIdx++) {
//        for (int varIdx = activeVars.nextSetBit(0); varIdx >= 0; varIdx = activeVars.nextSetBit(varIdx + 1)) {
//            monitors[varIdx].freeze();
//            int numDeltaSize = monitors[varIdx].sizeApproximation();
//            if (numDeltaSize != 0) {
//                // 变量发生改变
////                deletedValues[varIdx].clear();
//                triggeringVars.add(varIdx);
//                // 只动变量论域改变的变量，触发变量和删值队列都更新一下
//                monitors[varIdx].forEachRemVal(onValRem.set(varIdx));
////                RD[varIdx].generateBitSet(D[varIdx]);
////                updatedVars.add(varIdx);
//            }
//            monitors[varIdx].unfreeze();
//
//            if (vars[varIdx].isInstantiated()) {
//                activeVars.clear(varIdx);
//            }
//        }
//    }
//
//    private void MakeAugmentingPath(int start) {
//        // Do a BFS and use visiting_ as a queue, with num_visited pointing
//        // at its begin() and num_to_visit its end().
//        // To switch to the augmenting path once a nonmatched value was found,
//        // we remember the BFS tree in variable_visited_from_.
//
//        // start传入的是变量
//        // 执行一个BFS并使用visiting_作为一个队列，num_visited指向它的begin()，
//        // num_to_visit指向它的end()。要在发现不匹配的值时切换到扩展路径，
//        // 我们需要记住variable_visited_from_中的BFS树
//        //
//        int num_to_visit = 0;
//        int num_visited = 0;
//        // Enqueue start.
//        // visit 里存的是变量
//        visiting_[num_to_visit++] = start;
////        variable_visited_[start] = true;
////        variable_visited_.set(start);
//        unVisitedVariables.clear(start);
//        variable_visited_from_[start] = -1;
//
//        while (num_visited < num_to_visit) {
//            // Dequeue node to visit.
//            int node = visiting_[num_visited++];
////            updateBitDom(node);
////            needVisitValues.setAfterAnd(D[node], unVisitedValues);
////            for (int valIdx = needVisitValues.firstSetBit(); valIdx != unVisitedValues.end(); valIdx = needVisitValues.nextSetBit(valIdx + 1)) {
//            for (int valIdx = RD[node].nextSetBit(0); valIdx >= 0; valIdx = RD[node].nextSetBit(valIdx + 1)) {
//                if (visitedValues.get(valIdx)) continue;
//                visitedValues.set(valIdx);
////                updateBitBel(valIdx);
////                if (val2Var[valIdx] == -1) {
//                if (!matchedValuesR.get(valIdx)) {
//                    // value_to_variable_[valIdx] ， value这个值未分配到变量，即是一个free
//                    // !! 这里可以改用bitSet 求原数据bitDom (successor_)
//                    // 与matching的余集(matching_bitVector[a]，表示a是否已matching出去了) 再按1取未匹配值，
//                    // 可以惰性取值，即先算两个集合的在特定位置的交：以matching_bv为长度foreach
//                    // （一般不会特别长两个数据结构可以用NaiveBitSet，如400皇后，|D|=400，只需要7个，
//                    // 做&后会得到一个或NaiveBitSet, LargeBitSet）
//                    // valIdx is not matched: change path from node to start, and return.
//                    // 未匹配值
//
//                    // !! 路线回溯怎么用bit表示。
//                    // !! 这里可以提前记一些scc或是路径
//                    int path_node = node;
//                    int path_value = valIdx;
//                    while (path_node != -1) {
////                        // 旧变量拿到旧匹配值
////                        int old_value = var2Val[path_node];
////                        // 旧变量拿到新匹配值
////                        var2Val[path_node] = path_value;
////                        val2Var[path_value] = path_node;
//
//                        // 旧变量拿到旧匹配值
//                        int old_value = var2ValR[path_node].get();
//                        // 旧变量拿到新匹配值
//                        var2ValR[path_node].set(path_value);
//                        val2VarR[path_value].set(path_node);
//
//                        // 回溯到上一个变量
//                        path_node = variable_visited_from_[path_node];
//                        // 由于这个变量传递下去是连贯的，可以检查连通生，做为下一个阶段的记录
//                        path_value = old_value;
//                    }
//
//                    freeNodesR.clear(valIdx);
////                    freeNode.remove(valIdx);
//                    matchedValuesR.set(valIdx);
////                    System.out.println(valIdx + " is not free");
//                    return;
//                } else {
//                    // Enqueue node matched to valIdx.
//                    // 若没有该值已经有匹配，但变量没有匹配
//
//                    // 先拿到这个值的匹配变量
////                    int next_node = val2Var[valIdx];
//                    int next_node = val2VarR[valIdx].get();
////                    variable_visited_.set(next_node);
//                    unVisitedVariables.clear(next_node);
////                    System.out.println(num_to_visit + "," + next_node);
//                    // 把这个变量加入队列中
//                    visiting_[num_to_visit++] = next_node;
//                    variable_visited_from_[next_node] = node;
//                    freeNodesR.clear(valIdx);
////                    freeNode.remove(valIdx);
//                    matchedValuesR.set(valIdx);
//                }
//            }
//        }
//    }
//
//    // 第一次调用
//    private void findMaximumMatching() throws ContradictionException {
////        // !! 可做增量
////        freeNode.fill();
//        for (int varIdx = 0; varIdx < arity; varIdx++) {
////            for (int varIdx = activeVars.nextSetBit(0); varIdx >=0 ; varIdx = activeVars.nextSetBit(varIdx + 1)) {
//            if (var2ValR[varIdx].get() == -1) {
//                visitedValues.clear();
//                unVisitedVariables.set();
//                MakeAugmentingPath(varIdx);
//            }
//            if (var2ValR[varIdx].get() == -1) {
//                // No augmenting path exists.
//                vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
//            }
//        }
//
////        System.out.println(Arrays.toString(var2Val));
////        System.out.println(Arrays.toString(val2Var));
//    }
//
//    protected void repairMatching(int SCCStartIndex) throws ContradictionException {
//        // repair max matching.
//        partition.setIteratorIndexBySCCStartIndex(SCCStartIndex);
//        while (partition.hasNext()) {
//            int varIdx = partition.next();
////            updateBitDom(varIdx);
//            int valIdx = var2ValR[varIdx].get();
//            // 值失效
//            if (valIdx == -1 || !RD[varIdx].get(valIdx)) {
//                var2ValR[varIdx].set(-1);
//                visitedValues.clear();
//                unVisitedVariables.set();
//                MakeAugmentingPath(varIdx);
//            }
//
//            //匹配失败退出
//            if (var2ValR[varIdx].get() == -1) {
//                vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
//            }
//        }
//        partition.disposeSCCIterator();
//    }
//
//    protected boolean propagate_SCC_Match() throws ContradictionException {
//        boolean res = false;
//        IntVar x, y;
//        // 匹配值清空
//        changedSCCStartIndex.clear();
//        triggeringVars.iterateValid();
//        while (triggeringVars.hasNextValid()) {
//            int xIdx = triggeringVars.next();
//            int valIdx = var2ValR[xIdx].get();
//
//            int sccStartIdx = partition.getSCCStartIndexByElement(xIdx);
//            x = vars[xIdx];
//
//            // valIdx失效
//            if (valIdx == -1 || !RD[xIdx].get(valIdx)) {
//                repairMatching(sccStartIdx);
//            }
//
//            if (x.isInstantiated() && !partition.isSingletonByStartIndex(sccStartIdx)) {
//                valIdx = var2ValR[xIdx].get();
//                int xVal = idx2Val[valIdx];
//                if (changedSCCStartIndex.contains(sccStartIdx)) {
//                    changedSCCStartIndex.remove(sccStartIdx);
//                }
//
//                //parition s into s1 s2 , from now on s = s2
//                partition.remove(xIdx);
////                System.out.println(partition);
//
//                partition.setIteratorIndexBySCCStartIndex(sccStartIdx);
//                while (partition.hasNext()) {
//                    int yIdx = partition.next();
//                    if (RD[yIdx].get(valIdx)) {
//                        y = vars[yIdx];
//                        res |= y.removeValue(xVal, aCause);
//                        removeValueR(yIdx, valIdx);
////                        recordRemoveVal(yIdx, valIdx);
////                        deletedValues[yIdx].add(valIdx);
//                    }
//                }
//                partition.disposeSCCIterator();
//
//                if (!partition.isSingletonByStartIndex(sccStartIdx)) {
//                    changedSCCStartIndex.add(sccStartIdx);
//                }
//
//            } else {
//                if (!partition.isSingletonByStartIndex(sccStartIdx)) {
//                    changedSCCStartIndex.add(sccStartIdx);
//                }
//            }
//        }
//        return res;
//    }
//
//    protected void resetData(SparseSet resetVars, SparseSet resetVals, boolean containsSink) {
////        maxDFS = 0;
////        cycles.clear();
////        DE.clear();
//        hasSCCSplit = false;
//
//        resetVals.iterateValid();
//        while (resetVals.hasNextValid()) {
//            int i = resetVals.next();
////            System.out.println("resetVal: " + i);
//            valLowLink[i] = Integer.MAX_VALUE;
//            valDFSNum[i] = Integer.MAX_VALUE;
//        }
//
//        resetVars.iterateValid();
//        while (resetVars.hasNextValid()) {
//            int i = resetVars.next();
////            System.out.println("resetVar: " + i);
//            varLowLink[i] = Integer.MAX_VALUE;
//            varDFSNum[i] = Integer.MAX_VALUE;
////            if (triggeringVars.contains(i)) {
////                var iter = deletedValues[i].iterator();
////                while (iter.hasNext()) {
////                    int valIdx = iter.next();
////                    if (resetVals.contains(valIdx))
////                        DE.push(getIntTuple2Long(i, valIdx));
////                }
////            }
//        }
//
//        if (containsSink) {
//            sinkDFSNum = Integer.MAX_VALUE;
//            sinkLowLink = Integer.MAX_VALUE;
//            sinkIsInStack = false;
//            sinkIsUnvisited = true;
//        }
//
//        unVisitedVariables.set();
//        unVisitedValues.set();
//    }
//
//    boolean findAllSCC(BitSet restri, SparseSet resVars) {
//        clearVarStack();
//        clearValStack();
//
//        findSingletons(restri, resVars);
////        System.out.println("restriction: " + restri);
////        System.out.println("partition: " + partition);
//        for (int varIdx = restri.nextSetBit(0); varIdx >= 0 && varIdx < arity; varIdx = restriction.nextSetBit(varIdx + 1)) {
////            if (unVisitedVariables.get(varIdx)) {
////                System.out.println(varIdx);
////            System.out.printf("out: %d\n", varIdx);
//            strongConnectVar(varIdx);
////            }
//        }
//        return false;
//    }
//
//    protected void findSingletons(BitSet restri, SparseSet resVars) {
////        singleton.clear();
//        resVars.iterateValid();
////        for (int i = 0; i < arity; i++) {
//        while (resVars.hasNextValid()) {
//            int i = resVars.next();
//            // 变量只有一个值，即只有匹配值
//            // 若匹配边由变量指向值，若D[x]=1则表示变量x只有一个出边即匹配边，没有入边，即满足singleton条件
//            IntVar v = vars[i];
//            if (v.getDomainSize() == 1 && !partition.isSingletonByElement(i)) {
////                varSCC[i] = nbSCC;
////                singleton.set(i);
////                int totalIdx = valIndex2TotalIndex(var2Val[i]);
//                restri.clear(i);
////                restri.clear(totalIdx);
//                partition.remove(i);
////                partition.remove(totalIdx);
////                nbSCC++;
//            }
//        }
//    }
//
//    protected boolean propagate_SCC_filter() throws ContradictionException {
//        boolean filter = false;
////        freeNodesR.generateBitSet(A);
////        System.out.println("changed: " + changedSCCStartIndex);
////        System.out.println("freeNodes: " + freeNodesR);
////        System.out.println("gamma: " + gammaMask);
////        System.out.println("A: " + A);
////        System.out.println("trigger: " + triggeringVars);
//        // for Zhang18
//        // 带gamma的分区总在第0个分区中，
//        // 若第0个分区changed并且freenode不为空。
////        if (changedSCCStartIndex.contains(0) && !freeNodesR.isEmpty()) {
////            // 有freeNodes才执行。在gamma区中过滤
////            int newSCCStart = distinguish();
////            // newSCCStart == -1 表示Gamma占据当前全部scc
////            if (newSCCStart != INDEX_OVERFLOW) {
////                filter |= filterDomainsGamma();
//////                // gamma分裂区中建图过滤
////                initiateMatrixAfterGamma(newSCCStart);
////                if (numSCCValues >= (numSCCDeleteValues << 1)) {
////                    if (earlyDetection()) {
////                        Measurer.enterSkip();
////                    } else {
////                        filter |= filterDomainsPartition(newSCCStart);
////                    }
////                } else {
////                    filter |= filterDomainsPartition(newSCCStart);
////                }
//////                filter |= filterDomainsPartition(newSCCStart);
////            }
////            changedSCCStartIndex.remove(0);
////        }
//        valsMask.clear();
//        resetData(0);
//        changedSCCStartIndex.iterateValid();
//        while (changedSCCStartIndex.hasNextValid()) {
//            int sccStartIndex = changedSCCStartIndex.next();
//            resetData(sccStartIndex);
////            valsMask
////            initiateMatrixOrdinary(sccStartIndex);
////            filter |= filterDomainsPartition(sccStartIndex);
//            findAllSCC(sccStartIndex, varsTmp);
//            filter |= filterDomains(varsMask, varsMask);
//        }
//        return filter;
//    }
//
//    private boolean filterDomains(SimpleBitSet varsMask, SimpleBitSet varsMask1) {
//        boolean filter = false;
////        filterVars.iterateValid();
////        while (filterVars.hasNextValid()) {
////            int varIdx = filterVars.next();
//        for (int varIdx = varsMask.nextSetBit(0); varIdx >= 0; varIdx = varsMask.nextSetBit(varIdx + 1))
//            IntVar v = vars[varIdx];
//        if (!v.isInstantiated()) {
//            filterVals.iterateValid();
//            while (filterVals.hasNextValid()) {
//                int valIdx = filterVals.next();
//                int k = idx2Val[valIdx];
////                int ub = v.getUB();
////                for (int k = v.getLB(); k <= ub; k = v.nextValue(k)) {
////                    int valIdx = val2Idx.get(k);
////                    System.out.println(varIdx+", "+valIdx);
//                if (!partition.inSameSCC(varIdx, valIdx + addArity)) {
//                    Measurer.enterP2();
//                    if (valIdx == var2Val[varIdx]) {
//                        int valNum = v.getDomainSize();
//                        Measurer.numDelValuesP2 += valNum - 1;
//                        filter |= v.instantiateTo(k, aCause);
////                            System.out.println("instantiate: " + varIdx + ", " + k);
//                    } else {
//                        ++Measurer.numDelValuesP2;
//                        filter |= v.removeValue(k, aCause);
////                            D[varIdx].clear(valIdx);
////                            System.out.println("second delete: " + varIdx + ", " + k);
//                    }
//                }
//            }
//        }
//    }
//        return filter;
//}
//
//    protected void resetData(int sccStartIdx) {
////        hasSCCSplit = false;
////        Arrays.fill(valLowLink, Integer.MAX_VALUE);
////        Arrays.fill(valDFSNum, Integer.MAX_VALUE);
////        Arrays.fill(varLowLink, Integer.MAX_VALUE);
////        Arrays.fill(varDFSNum, Integer.MAX_VALUE);
////        sinkDFSNum = Integer.MAX_VALUE;
////        sinkLowLink = Integer.MAX_VALUE;
////        sinkIsInStack = false;
////        sinkIsUnvisited = true;
////        unVisitedVariables.set();
////        unVisitedValues.set();
//        hasSCCSplit = false;
//
//        partition.setIteratorIndexBySCCStartIndex(sccStartIdx);
//        while (partition.hasNext()) {
//            int varIdx = partition.next();
//            valsMask.or(RD[varIdx]);
//            varLowLink[varIdx] = Integer.MAX_VALUE;
//            varDFSNum[varIdx] = Integer.MAX_VALUE;
//            // varIdx 只可能在两个子分区中，checked和unknown
////            IntVar v = vars[varIdx];
//        }
//        partition.disposeSCCIterator();
//
//        sinkDFSNum = Integer.MAX_VALUE;
//        sinkLowLink = Integer.MAX_VALUE;
//        sinkIsInStack = false;
//        sinkIsUnvisited = true;
//
//        for (int i = valsMask.nextSetBit(0); i >= 0;
//             i = valsMask.nextSetBit(i + 1)) {
//            valLowLink[i] = Integer.MAX_VALUE;
//            valDFSNum[i] = Integer.MAX_VALUE;
//        }
//
//        unVisitedVariables.set();
//        unVisitedValues.set();
//    }
//
//
//    //***********************************************************************************
//    // PRUNING
//    //***********************************************************************************
//    // 只有changedSCCStartIndex包括索引0才会触发这个传播,反回除去gamma的新scc
//    // 返回新SCCStartIndex，如果返回-1表示该SCC全部为gamma
//
//
////    // 带Gamma的SCC才如下建模
////    private void initiateMatrixGamma() {
////        // 重置两个矩阵
////        // 不包括gamma子分区
////        partition.setIteratorIndexAfterGamma();
////        while (partition.hasNext()) {
////            int varIdx = partition.next();
//////            updateBitDom(varIdx);
////            // 从变量id拿到匹配值再拿到该值所能到达的变量mask
////            int valIdx = var2ValR[varIdx].get();
//////            updateBitBel(valIdx);
////            graphLinkedMatrix[varIdx].setAfterMinus(RB[valIdx], gammaMask);
////            graphLinkedMatrix[varIdx].clear(varIdx);
////            graphLinkedFrontier[varIdx].set(graphLinkedMatrix[varIdx]);
//////            System.out.println("------graphLinkedMatrix[" + varIdx + "]------");
//////            System.out.println(graphLinkedMatrix[varIdx]);
//////            System.out.println(graphLinkedFrontier[varIdx]);
////        }
////
////        partition.disposeSCCIterator();
////    }
//
//    // 只用来过滤带有Gamma的SCC，全程不用算scc
//    private boolean filterDomainsGamma() throws ContradictionException {
//        boolean filter = false;
//        partition.setIteratorIndexBySCCStartIndex(0);
//        while (partition.hasNext()) {
//            int varIdx = partition.next();
//            // varIdx 只可能在两个子分区中，checked和unknown
//            IntVar v = vars[varIdx];
//            for (int valIdx = RD[varIdx].nextSetBit(0); valIdx >= 0; valIdx = RD[varIdx].nextSetBit(valIdx + 1)) {
//                if (!A.get(valIdx)) {
//                    // 变量在Gamma,值不在A
//                    ++Measurer.numDelValuesP1;
//                    Measurer.enterP1();
//                    int k = idx2Val[valIdx];
//                    filter |= v.removeValue(k, aCause);
//                    removeValueR(varIdx, valIdx);
////                    recordRemoveVal(varIdx, valIdx);
////                    if (numCall == 694)
////                        System.out.println("first delete1: " + varIdx + ", " + valIdx);
//                }
//            }
//        }
//        partition.disposeSCCIterator();
//        return filter;
//    }
//
//    private boolean filterDomainsPartition(int sccStartIndex) throws ContradictionException {
//        boolean filter = false;
//        partition.setIteratorIndexBySCCStartIndex(sccStartIndex);
//        while (partition.hasNext()) {
//            // 分为三个分区：sccStart,checked,unknown,moved,sccEnd
//            int varIdx = partition.nextAndSplitWhenMeetingUnknownAndMoved();
//            // varIdx 只可能在两个子分区中，checked和unknown
//            IntVar v = vars[varIdx];
//            if (!v.isInstantiated()) {
//                int matchedVal = var2ValR[varIdx].get();
//                int k = idx2Val[matchedVal];
//                // 先验证匹配值，再验证其它值
//                if (!checkSCC(varIdx, matchedVal)) {
//                    Measurer.enterP2();
//                    int valNum = v.getDomainSize();
//                    Measurer.numDelValuesP2 += valNum - 1;
//                    filter |= v.instantiateTo(k, aCause);
//                    instantiateToR(varIdx, matchedVal);
////                    recordInstVar(varIdx, matchedVal);
//                    partition.removeCurrentToTail();
////                    if (numCall == 694)
////                        System.out.println("instantiate  : " + varIdx + ", " + matchedVal);
////                    continue;
//                } else {
//                    // 匹配值在SCC中，表示变量论域至少两个值，且至少有一个值在SCC中
//                    partition.setCurrentConnected();
//                    // 再验证其它值
//                    for (int valIdx = RD[varIdx].nextSetBit(0); valIdx >= 0; valIdx = RD[varIdx].nextSetBit(valIdx + 1)) {
//                        // valIdx 可能在三个子分区内：connected，unknown和moved
//                        // 在connected分区中不用验证，
//                        // 在unknown分区中的需要检测scc
//                        // 在moved分区中的直接移除
//
//                        int varIdx2 = val2VarR[valIdx].get();
//                        if (varIdx != varIdx2) {
//                            k = idx2Val[valIdx];
//                            if (partition.varInUnknown(varIdx2)) {
//                                // 在Unknown分区中，需检查，能连通就加入Connected，不通连通就放入Moved分区
//                                if (!checkSCC(varIdx, valIdx)) {
//                                    Measurer.enterP2();
//                                    ++Measurer.numDelValuesP2;
//                                    filter |= v.removeValue(k, aCause);
//                                    removeValueR(varIdx, valIdx);
////                                    recordRemoveVal(varIdx, valIdx);
//                                    // varIdx2未分裂，将varIdx2移入tmp分区中
//                                    partition.addMoved(varIdx2);
////                                    if (numCall == 694)
////                                        System.out.println("second delete1: " + varIdx + ", " + valIdx);
//                                } else {
//                                    partition.addConnected(varIdx2);
//                                }
//                            } else if (partition.varInMoved(varIdx2)) {
//                                // var2在moved子分区,
//                                Measurer.enterP2();
//                                ++Measurer.numDelValuesP2;
//                                filter |= v.removeValue(k, aCause);
//                                removeValueR(varIdx, valIdx);
////                                recordRemoveVal(varIdx, valIdx);
//                                //                                    if (partition.canMove(varIdx2)) {
////                                if (numCall == 694)
////                                    System.out.println("second delete2: " + varIdx + ", " + valIdx);
//
////                                if (partition.canMove(varIdx2)) {
////                                    // varIdx2未分裂，将varIdx2移入tmp分区中
////                                    partition.addMoved(varIdx2);
////                                }
//                            } else if (partition.varNotInSameSCC(varIdx2)) {
//                                // var2在moved子分区,
//                                Measurer.enterP2();
//                                ++Measurer.numDelValuesP2;
//                                filter |= v.removeValue(k, aCause);
//                                removeValueR(varIdx, valIdx);
////                                recordRemoveVal(varIdx, valIdx);
////                                if (numCall == 694)
////                                    System.out.println("second delete3: " + varIdx + ", " + valIdx);
//
//                            }
//
//                            // 如果在Connected分区或在其它SCC中，跳过该值
//
//                        }
//                    }
//                }
//            }
//        }
//        partition.disposeSCCIterator();
//        return filter;
//    }
//
//
//    @Override
//    protected void removeValueR(int varIdx, int valIdx) {
//        RD[varIdx].clear(valIdx);
//        RB[valIdx].clear(varIdx);
////        if (varIdx == 12)
////            System.out.printf("remove Value: (%d, %d)\n", varIdx, valIdx);
//    }
//
//    @Override
//    protected void instantiateToR(int varIdx, int valIdx) {
//        for (int i = RD[varIdx].nextSetBit(0); i >= 0; i = RD[varIdx].nextSetBit(i + 1)) {
//            RB[i].clear(varIdx);
//        }
//        RD[varIdx].clear();
//        RD[varIdx].set(valIdx);
//        RB[valIdx].clear();
//        RB[valIdx].set(varIdx);
////        if (varIdx == 12)
////            System.out.printf("instan Value: (%d, %d)\n", varIdx, valIdx);
//    }
//
//    protected void strongConnectVar(int curNode) {
//        pushVarStack(curNode);
//        varDFSNum[curNode] = maxDFS;
//        varLowLink[curNode] = maxDFS;
//        maxDFS++;
//        unVisitedVariables.clear(curNode);
//
////         p2
//        long values = 0;
//        int newNode = 0, iBase = 0;
//        int matchedVal = var2Val[curNode];
//        int i = 0;
//        for (int iWord = D[curNode].firstSetIndex(); iWord <= D[curNode].lastSetIndex(); ++iWord) {
//            values = D[curNode].getWord(iWord) & valIsInStack.getWord(iWord);
//            iBase = iWord * 64;
////            System.out.println(D[curNode]);
////            System.out.println(curNode + ": " + Long.toBinaryString(D[curNode].getWord(iWord)) + ": " + Long.toBinaryString(valIsInStack.getWord(iWord)) + ": " + Long.toBinaryString(values));
//
//            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
//                newNode = iBase + i;
//                if (newNode == matchedVal) continue;
//                varLowLink[curNode] = Math.min(varLowLink[curNode], valDFSNum[newNode]);
////                if (numCall != 0 && DE.size() != 0 && !unconnected) DETest(valLowLink[newNode], maxDFS - 1);
//            }
//
//            values = D[curNode].getWord(iWord) & unVisitedValues.getWord(iWord);
//            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
//                newNode = iBase + i;
//                strongConnectVal(newNode);
//                varLowLink[curNode] = Math.min(varLowLink[curNode], valLowLink[newNode]);
//                values &= unVisitedValues.getWord(iWord);
//            }
//        }
//
//        if (varLowLink[curNode] == varDFSNum[curNode]) {
//            if (varLowLink[curNode] > 0 || valIsInStack.size() + varIsInStack.size() > 0) {
//                hasSCCSplit = true;
//            }
//            if (hasSCCSplit) {
//                processSCC(varDFSNum[curNode]);
//            }
//        }
//////        System.out.println("back");
////        if (numCall != 0 && !unconnected && (DE.size() == 0)) {
//////            System.out.println("xixi");
////            isSkiped = true;
////            return;
////        }
//    }
//
//    protected void strongConnectVal(int curNode) {
//        pushValStack(curNode);
//        valDFSNum[curNode] = maxDFS;
//        valLowLink[curNode] = maxDFS;
//        maxDFS++;
//        unVisitedValues.clear(curNode);
//        int matchedVar = val2Var[curNode];
//        if (matchedVar != -1) {
//            //have matched variable
////            System.out.println("scValtoVar: " + (addArity + curNode) + ", " + matchedVar + ", " + unVisitedVariables.get(matchedVar));
////            System.out.println((addArity + curNode) + ", " + matchedVar + ", " + unVisitedVariables.get(matchedVar));
//            if (!unVisitedVariables.get(matchedVar)) {
//                if (varIsInStack.get(matchedVar)) {
//                    valLowLink[curNode] = Math.min(valLowLink[curNode], varDFSNum[matchedVar]);
////                    if (numCall != 0 && DE.size() != 0 && !unconnected) DETest(varLowLink[matchedVar], maxDFS - 1);
//                }
//            } else {
//                strongConnectVar(matchedVar);
//                valLowLink[curNode] = Math.min(valLowLink[curNode], varLowLink[matchedVar]);
//            }
//        } else {
//            //free node successor node is sink node
////            System.out.println("scValtoSink: " + (addArity + curNode) + ", " + arity + ", " + sinkIsUnvisited);
////            System.out.println((addArity + curNode) + ", " + arity + ", " + sinkIsUnvisited);
//            if (!sinkIsUnvisited) {
//                if (sinkIsInStack) {
//                    valLowLink[curNode] = Math.min(valLowLink[curNode], sinkDFSNum);
////                    if (numCall != 0 && DE.size() != 0 && !unconnected) DETest(sinkLowLink, maxDFS - 1);
//                }
//            } else {
//                strongConnectSink();
//                valLowLink[curNode] = Math.min(valLowLink[curNode], sinkLowLink);
//            }
//        }
////        Iterator<Integer> iterator = graph.getSuccOf(curNode).iterator();
////        //B[]
////        while (iterator.hasNext()) {
////            int newNode = iterator.next();
//////            System.out.println(curNode + ", " + newNode + ", " + unvisited.get(newNode));
////            if (!unVisitedVariables.get(newNode)) {
////                if (valIsInStack.get(newNode)) {
////                    valLowLink[curNode] = Math.min(valLowLink[curNode], varDFSNum[newNode]);
////                }
////            } else {
////                // 判断一下sink节点
////                strongConnectR(newNode);
////                lowLink[curNode] = Math.min(lowLink[curNode], lowLink[newNode]);
////            }
////        }
//
////        System.out.println(curNode + " has no nei " + lowLink[curNode] + ", " + DFSNum[curNode]);
//        if (valLowLink[curNode] == valDFSNum[curNode]) {
//            if (valLowLink[curNode] > 0 || valIsInStack.size() + varIsInStack.size() > 0) {
//                hasSCCSplit = true;
//            }
//            if (hasSCCSplit) {
//                processSCC(valDFSNum[curNode]);
//            }
//        }
//
////        if (numCall != 0 && !unconnected && (DE.size() == 0)) {
//////            System.out.println("xixi");
////            isSkiped = true;
////            return;
////        }
////        System.out.println("back");
//    }
//
//    protected void strongConnectSink() {
//        sinkIsInStack = true;
//        sinkDFSNum = maxDFS;
//        sinkLowLink = maxDFS;
//        maxDFS++;
//        sinkIsUnvisited = false;
//
//        long values = 0;
//        int newNode = 0, iBase = 0;
//        int i = 0;
//        for (int iWord = matchedValues.firstSetIndex(); iWord <= matchedValues.lastSetIndex(); ++iWord) {
//            values = matchedValues.getWord(iWord) & ~unVisitedValues.getWord(iWord) & valIsInStack.getWord(iWord);
//            iBase = iWord * 64;
//            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
//                newNode = iBase + i;
//                sinkLowLink = Math.min(sinkLowLink, valDFSNum[newNode]);
////                if (numCall != 0 && DE.size() != 0 && !unconnected) DETest(valLowLink[newNode], maxDFS - 1);
//            }
//
////            values = matchedValues.getWord(iWord) & unVisitedValues.getWord(iWord);
////            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
////                newNode = iBase + i;
////                strongConnectVal(newNode);
////                sinkLowLink = Math.min(sinkLowLink, valLowLink[newNode]);
////                values &= unVisitedValues.getWord(iWord);
////            }
//
//            values = matchedValues.getWord(iWord) & unVisitedValues.getWord(iWord);
//            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
//                newNode = iBase + i;
//                strongConnectVal(newNode);
//                sinkLowLink = Math.min(sinkLowLink, valLowLink[newNode]);
//                values &= unVisitedValues.getWord(iWord);
//            }
//        }
//
////        System.out.println(curNode + " has no nei " + lowLink[curNode] + ", " + DFSNum[curNode]);
//        if (sinkLowLink == sinkDFSNum) {
//            if (sinkLowLink > 0 || sinkIsInStack || valIsInStack.size() + varIsInStack.size() > 0) {
//                hasSCCSplit = true;
//            }
//            if (hasSCCSplit) {
//                processSCC(sinkDFSNum);
//            }
//        }
//
////        if (numCall != 0 && !unconnected && (DE.size() == 0)) {
//////            System.out.println("xixi");
////            isSkiped = true;
////            return;
////        }
////        System.out.println("back");
//    }
//
//    protected void processSCC(int rootNum) {
////        for (int valIdx = valIsInStack.firstSetBit(); valIdx !=INaiveBitSet.INDEX_OVERFLOW; valIdx=valIsInStack.++) {
////
////        }
////        System.out.println("scc: " + rootNum);
//        int stackNode = -1;
////        sccSize = 0;
////        int limit;
//        if (varStackIdx > 0 && varDFSNum[varStack[varStackIdx - 1]] >= rootNum) {
//            int x = getTopVarStack();
//            partition.resetLimitByElement(x);
//        } else if (valStackIdx > 0 && valDFSNum[valStack[valStackIdx - 1]] >= rootNum) {
//            int x = getTopValStack();
//            partition.resetLimitByElement(valIndex2TotalIndex(x));
//        }
////        if (valStackIdx != 0) {
////            stackNode = valStack[valStackIdx - 1];
//        while (valStackIdx > 0 && valDFSNum[valStack[valStackIdx - 1]] >= rootNum) {
//            stackNode = popValStack();
////            System.out.println("pop val: " + (addArity + stackNode) + ", " + stackNode + ", " + nbSCC + "," + valDFSNum[stackNode]);
//            partition.add(valIndex2TotalIndex(stackNode));
//            restriction.clear(valIndex2TotalIndex(stackNode));
////            valSCC[stackNode] = nbSCC;
////            sccSize++;
//        }
////        }
//
////        if (varStackIdx != 0) {
////            stackNode = varStack[varStackIdx - 1];
//        while (varStackIdx > 0 && varDFSNum[varStack[varStackIdx - 1]] >= rootNum) {
//            stackNode = popVarStack();
////            System.out.println("pop var: " + stackNode + ", " + nbSCC + "," + varDFSNum[stackNode]);
////            varSCC[stackNode] = nbSCC;
//            restriction.clear(stackNode);
//            partition.add(stackNode);
////            sccSize++;
//        }
////        }
//
//        if (sinkIsInStack && sinkDFSNum >= rootNum) {
//            partition.add(arity);
//            restriction.clear(arity);
//            sinkIsInStack = false;
//        }
//
//        partition.setSplit();
////        unconnected = true;
////        System.out.println("partition: " + partition);
////        nbSCC++;
//    }
//
//    protected void pushVarStack(int v) {
//        varStack[varStackIdx++] = v;
//        varIsInStack.set(v);
//    }
//
//    protected void clearVarStack() {
//        varIsInStack.clear();
//        varStackIdx = 0;
//    }
//
//    protected int popVarStack() {
//        int x = varStack[--varStackIdx];
//        varIsInStack.clear(x);
//        return x;
//    }
//
//    protected void pushValStack(int v) {
//        valStack[valStackIdx++] = v;
//        valIsInStack.set(v);
//    }
//
//    protected void clearValStack() {
//        valIsInStack.clear();
//        valStackIdx = 0;
//    }
//
//    protected int popValStack() {
//        int x = valStack[--valStackIdx];
//        valIsInStack.clear(x);
//        return x;
//    }
//
//    public static int nextSetBit(long words, int bitIndex) {
//        return Long.numberOfTrailingZeros(words & -1L << bitIndex);
//    }
//
//    protected int getTopVarStack() {
//        return varStack[varStackIdx - 1];
//    }
//
//    protected int getTopValStack() {
//        return valStack[valStackIdx - 1];
//    }
//
////    int totalIndex2ValIndex(int totalIndex) {
////        return totalIndex - addArity;
////    }
//
////    int valIndex2TotalIndex(int valIndex) {
////        return valIndex + addArity;
////    }
//
//}
