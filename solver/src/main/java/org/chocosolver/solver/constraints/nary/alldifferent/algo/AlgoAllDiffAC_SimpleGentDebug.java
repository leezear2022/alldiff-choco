//package org.chocosolver.solver.constraints.nary.alldifferent.algo;
//
////import org.chocosolver.amtf.Measurer;
//
//import gnu.trove.iterator.TIntIntIterator;
//import gnu.trove.map.hash.TIntIntHashMap;
//import org.chocosolver.memory.IEnvironment;
//import org.chocosolver.memory.IStateBitSet;
//import org.chocosolver.memory.IStateInt;
//import org.chocosolver.solver.ICause;
//import org.chocosolver.solver.Model;
//import org.chocosolver.solver.exception.ContradictionException;
//import org.chocosolver.solver.variables.IntVar;
//import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
//import org.chocosolver.util.iterators.DisposableValueIterator;
//import org.chocosolver.util.objects.IStateBitSetPartition;
//import org.chocosolver.util.objects.Measurer;
//import org.chocosolver.util.objects.SimpleBitSet;
//import org.chocosolver.util.objects.SparseSet;
//import org.chocosolver.util.procedure.UnaryIntProcedure;
//
//import java.util.Arrays;
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
//public class AlgoAllDiffAC_SimpleGentDebug extends AlgoAllDiffAC_Simple {
//
//    //***********************************************************************************
//    // VARIABLES
//    //***********************************************************************************
//    // 约束的个数
//    static public int num = 0;
//    static public int INDEX_OVERFLOW = -1;
//    static long numCall =-1;
//    // 约束的编号
//    private int id;
//    private int arity;
//    private IntVar[] vars;
//    private ICause aCause;
//    // 新增一点（视为变量）
////    private int addArity;
//    // 自由值集合
//    private SparseSet freeNode;
//    // 以下是bit版本所需数据结构========================
//    // numValue是二部图中取值编号的个数，numBit是二部图的最大边数
//    private int numValues;
//    // 值到索引
//    private int[] idx2Val;
//    // 索引到值
//    private TIntIntHashMap val2Idx;
//    // Xc-Γ(A)
//    private SparseSet notGamma;
//    // Dc-A
//    private SparseSet notA;
//    // 与值相连的变量
//    private SimpleBitSet[] B;
//    private SimpleBitSet[] D;
//
//    // 已访问过的变量和值
////    private SimpleBitSet visitedVariables;
//    private SimpleBitSet unVisitedVariables;
//    //    private SimpleBitSet value_visited_;
////    private SimpleBitSet unVisitedValues;
////    private SimpleBitSet needVisitValues;
//    private BitSet visitedValues;
//    //    private SparseSet unVisitedValues;
//    //    private BitSet needVisitValues;
//    //    private SimpleBitSet unMatchedValues;
////    private SimpleBitSet matchedValues;
//    private IStateBitSet matchedValuesR;
//    private SimpleBitSet freeNodes;
//    //    private SimpleBitSet matchedMasks;
////    private SimpleBitSet varSingletonMask;
////    private SimpleBitSet valSingletonMask;
////    private SimpleBitSet varTmpMask;
//    // matching
////    private int[] val2Var;
////    private int[] var2Val;
//    private IStateInt[] val2VarR;
//    private IStateInt[] var2ValR;
//    // 记录队列
//    private int[] visiting_;
//    private int[] variable_visited_from_;
//
//    // 变量到变量的连通性
//    // 对于惰性算法，记录是否知道-变量到变量的连通性
//    private SimpleBitSet[] graphLinkedMatrix;
//    private SimpleBitSet[] graphLinkedFrontier;
//
//    // !! 记录gamma的前沿
//    private SimpleBitSet gammaFrontier;
//    // 记录gamma的bitset
//    private SimpleBitSet gammaMask;
//
//    // 记录scc
////    private BitSet[] sccMatrix;
//    protected boolean initialPropagation = true;
//    //    protected RSetPartition partition;
////    protected RSetPartition partition;
//    protected IStateBitSetPartition partition;
//    private SparseSet triggeringVars;
//    //    private SparseSet triggeringVals;
//    private IIntDeltaMonitor[] monitors;
//    private UnaryIntProcedure<Integer> onValRem;
//    private SparseSet[] deletedValues;
//    protected SparseSet varsTmp;
//    private SparseSet changedSCCStartIndex;
//    protected boolean unconnected = false;
//    protected boolean isSkiped = false;
//
//    // 懒计算域更新
//    private SparseSet updatedVars;
//    private SparseSet updatedVals;
//
//    long startTime;
//    private IEnvironment env;
//    //    private int endBitIndex = 64;
//    // for delta update
////    protected IIntDeltaMonitor[] monitors;
////    private UnaryIntProcedure<Integer> onValRem;
////    private boolean initialProp = true;
////
////    //    // for backtrack
////    IEnvironment env;
//    IStateBitSet[] RB;
//    IStateBitSet[] RD;
//    // if all a in var x val2Idx[a] = a then DomIsRagular[x] = true
//    boolean[] domIsRegular;
//    int lastBindVar = INDEX_OVERFLOW;
//
//    //***********************************************************************************
//    // CONSTRUCTORS
//    //***********************************************************************************
//    public AlgoAllDiffAC_SimpleGentDebug(IntVar[] variables, ICause cause, Model model) {
//        super(variables, cause, model.getEnvironment());
//        id = num++;
//        env = model.getEnvironment();
//        vars = variables;
//        aCause = cause;
//        arity = vars.length;
//        val2Idx = new TIntIntHashMap();
//
//        // 先将从0开始的变量论域进行编码，只编一个变量
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            if (v.getLB() == 0) {
//                for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
//                    if (!val2Idx.containsKey(j)) {
//                        val2Idx.put(j, val2Idx.size());
//                    }
//                }
//                break;
//            }
//        }
//
//        // 全部从头编码
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
//                if (!val2Idx.containsKey(j)) {
//                    val2Idx.put(j, val2Idx.size());
//                }
//            }
//        }
//
//        numValues = val2Idx.size();
//        idx2Val = new int[numValues];
//        TIntIntIterator it = val2Idx.iterator();
//        while (it.hasNext()) {
//            it.advance();
//            idx2Val[it.value()] = it.key();
//        }
//
//        // System.out.println("-----------idx2Val-----------");
//        // System.out.println(Arrays.toString(idx2Val));
//        // for backtracking
//        B = new SimpleBitSet[numValues];
//        RB = new IStateBitSet[numValues];
//        for (int i = 0; i < numValues; ++i) {
//            B[i] = new SimpleBitSet(arity);
//            RB[i] = env.makeBitSet(arity);
//        }
//
//        D = new SimpleBitSet[arity];
//        RD = new IStateBitSet[arity];
//        domIsRegular = new boolean[arity];
//        for (int i = 0; i < arity; i++) {
//            D[i] = new SimpleBitSet(numValues);
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
//                B[valIdx].set(i);
//                RD[i].set(valIdx);
//                D[i].set(valIdx);
//            }
//            vit.dispose();
//        }
//
//        // 记录访问过的变量
//        visiting_ = new int[arity];
//        unVisitedVariables = new SimpleBitSet(arity);
//        // 变量的前驱变量，若前驱变量是-1，则表示无前驱变量，就是第一个变量
//        variable_visited_from_ = new int[arity];
//        visitedValues = new BitSet(numValues);
////        matchedValues = new SimpleBitSet(numValues);
//        matchedValuesR = env.makeBitSet(numValues);
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
//        freeNode = new SparseSet(numValues);
//        gammaFrontier = new SimpleBitSet(arity);
//        gammaMask = new SimpleBitSet(arity);
//        notGamma = new SparseSet(arity);
//        notA = new SparseSet(numValues);
//
//        graphLinkedMatrix = new SimpleBitSet[arity];
//        graphLinkedFrontier = new SimpleBitSet[arity];
//        for (int i = 0; i < arity; ++i) {
//            graphLinkedMatrix[i] = new SimpleBitSet(arity);
//            graphLinkedFrontier[i] = new SimpleBitSet(arity);
//        }
//
//        // for Gent algorithm
//        partition = new IStateBitSetPartition(arity, env);
//        triggeringVars = new SparseSet(arity);
////        triggeringVals = new SparseSet(numValues);
//        // 已懒更新的变量/值
//        updatedVars = new SparseSet(arity);
//        updatedVals = new SparseSet(numValues);
//        varsTmp = new SparseSet(arity);
//        changedSCCStartIndex = new SparseSet(arity);
//        monitors = new IIntDeltaMonitor[vars.length];
//        for (int i = 0; i < vars.length; i++) {
//            monitors[i] = vars[i].monitorDelta(cause);
//        }
//        onValRem = makeProcedure();
//
//        deletedValues = new SparseSet[arity];
//        for (int i = 0; i < arity; i++) {
//            deletedValues[i] = new SparseSet(numValues);
//        }
//    }
//
//    protected UnaryIntProcedure<Integer> makeProcedure() {
//        return new UnaryIntProcedure<Integer>() {
//            int varIdx;
//            IntVar v;
//            int matchedVal = -1;
//
//            @Override
//            public UnaryIntProcedure set(Integer o) {
//                varIdx = o;
//                v = vars[varIdx];
//                matchedVal = var2ValR[varIdx].get();
//                return this;
//            }
//
//            @Override
//            public void execute(int i) {
////                if (!triggeringVars.contains(var)) {
////                    triggeringVars.add(var);
////                    deletedValues[var].clear();
////                }
//                int valIdx = domIsRegular[varIdx] ? i : val2Idx.get(i);
////                if (!triggeringVals.contains(valIdx)) {
////                    triggeringVals.add(valIdx);
////                }
//
//                // 删的值是匹配值，清理匹配
//                if (valIdx == matchedVal) {
//                    var2ValR[varIdx].set(-1);
//                    val2VarR[valIdx].set(-1);
//                    matchedValuesR.clear(valIdx);
//                }
//
//                deletedValues[varIdx].add(valIdx);
//                RB[valIdx].clear(varIdx);
//                RD[varIdx].clear(valIdx);
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
//        System.out.println("----------------" + id + " propagate: " + (++numCall) + "----------------");
//        printDomains();
//        boolean filter = false;
//        Measurer.enterProp();
//        System.out.println(partition);
//        if (initialPropagation) {
////            triggeringVals.fill();
//            triggeringVars.fill();
//            updatedVars.fill();
//            updatedVals.fill();
//
//            startTime = System.nanoTime();
//            findMaximumMatching();
//            Measurer.matchingTime += System.nanoTime() - startTime;
//
//            System.out.println("matching: " + Arrays.toString(var2ValR));
//
//            startTime = System.nanoTime();
//            initiateMatrix(0);
//            filter = filterDomains(0);
//            Measurer.filterTime += System.nanoTime() - startTime;
//
//            initialPropagation = false;
//        } else {
//
//            deltaUpdate();
//
//            startTime = System.nanoTime();
//            filter |= propagate_SCC_Match();
//            Measurer.matchingTime += System.nanoTime() - startTime;
//            System.out.println("matching: " + Arrays.toString(var2ValR));
//
//            startTime = System.nanoTime();
//            System.out.println("updvar:" + updatedVars);
//            System.out.println("updval:" + updatedVals);
//            filter |= propagate_SCC_filter();
//            System.out.println("updvar2:" + updatedVars);
//            System.out.println("updval2:" + updatedVals);
////            System.out.println(partition);
//            Measurer.filterTime += System.nanoTime() - startTime;
//        }
////        for (int i = 0; i < arity; i++) {
////            RD[i].getWord()
////        }
////        startTime = System.nanoTime();
////        findMaximumMatching();
////        Measurer.matchingTime += System.nanoTime() - startTime;
//
////        startTime = System.nanoTime();
////        filter = filter();
////        Measurer.filterTime += System.nanoTime() - startTime;
//        return filter;
//    }
//
//    //***********************************************************************************
//    // Initialization
//    //***********************************************************************************
//
//
////    protected UnaryIntProcedure<Integer> makeProcedure() {
////        return new UnaryIntProcedure<Integer>() {
////            int var;
////            int valIdx;
////
////            @Override
////            public UnaryIntProcedure set(Integer o) {
////                var = o;
////                return this;
////            }
////
////            @Override
////            public void execute(int i) throws ContradictionException {
//////                DE.push(new IntTuple2(var, val2Idx.get(i) + addArity));
//////                IntVar v = vars[var];
////                valIdx = val2Idx.get(i);
////                RD[var].clear(valIdx);
////                RB[valIdx].clear(var);
//////                System.out.println(vars[var].getName() + "," + var + ", " + i + " = " + v.contains(i) + ", size = " + v.getDomainSize());
////            }
////        };
////    }
//
//    private void printDomains() {
//        // 填充B和D
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            System.out.println(D[i]);
//            System.out.println(v);
//        }
//    }
//
//    private void printBitDomains() {
//        for (int i = 0; i < numValues; ++i) {
//            System.out.println("val " + "i: " + B[i]);
//        }
//
//        IntVar v;
//        // 填充B和D
//        for (int i = 0; i < arity; ++i) {
//            v = vars[i];
//            System.out.println("val " + "i: " + D[i]);
//            System.out.println(v);
//        }
//    }
//
//
//    // 都不要了，改成懒计算。
//    private void fillBAndD(SparseSet changedVars, SparseSet changedVals) {
//        // 应该大范围更新
//        changedVars.iterateValid();
//        while (changedVars.hasNextValid()) {
//            int v = changedVars.next();
//            RD[v].generateBitSet(D[v]);
//            updatedVars.add(v);
//        }
//
//        changedVals.iterateValid();
//        while (changedVals.hasNextValid()) {
//            int a = changedVals.next();
//            RB[a].generateBitSet(B[a]);
//            updatedVals.add(a);
//        }
//    }
//
//    // 初始化RB和RD填充B和D
//    private void initialBDRBAndRD() {
//        // 填充B和D
//        for (int i = 0; i < numValues; ++i) {
//            B[i].clear();
//            RB[i].clear();
//        }
//
//        for (int i = 0; i < arity; ++i) {
//            D[i].clear();
//            RD[i].clear();
//            IntVar v = vars[i];
//            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
//                int valIdx = domIsRegular[i] ? j : val2Idx.get(j);
//                D[i].set(valIdx);
//                RD[i].set(valIdx);
//                B[valIdx].set(i);
//                RB[valIdx].set(i);
//            }
//        }
//    }
//
//    private void fill(int varIdx) {
//        // 填充RB和RD
////        for (int i = 0; i < arity; ++i) {
//        RD[varIdx].clear();
//        IntVar v = vars[varIdx];
//        if (domIsRegular[varIdx]) {
//            for (int i = v.getLB(), ub = v.getUB(); i <= ub; i = v.nextValue(i)) {
//                RD[varIdx].set(i);
//            }
//        } else {
//            for (int i = v.getLB(), ub = v.getUB(); i <= ub; i = v.nextValue(i)) {
//                RD[varIdx].set(val2Idx.get(i));
//            }
//        }
//
//    }
//
//    private void fillBitDBAfterInst(int varIdx, int valIdx) throws ContradictionException {
//        // 只在变量varIdx赋值后调用
//        D[varIdx].clear();
//        RD[varIdx].clear();
//        D[varIdx].set(valIdx);
//        RD[varIdx].set(valIdx);
//
//        // valIdx赋值的变量论域中都除去
//        for (int yIdx = RB[valIdx].nextSetBit(0); yIdx > 0; yIdx = RB[valIdx].nextSetBit(yIdx + 1)) {
//            if (yIdx != varIdx) {
////                updateBitDom(yIdx);
//                System.out.println("remove: " + yIdx + ", " + valIdx);
//                IntVar y = vars[yIdx];
//                int xVal = idx2Val[varIdx];
//                boolean res = y.removeValue(xVal, aCause);
//                removeValue(yIdx, valIdx);
//                deletedValues[yIdx].add(valIdx);
//            }
//        }
//    }
//
//    private void deltaUpdate() throws ContradictionException {
//        // 触发队列和更新队列
//        triggeringVars.clear();
////        triggeringVals.clear();
//        updatedVars.clear();
//        updatedVals.clear();
////        matchedValues.clear();
////        lastBindVar = INDEX_OVERFLOW;
//
//        for (int varIdx = 0; varIdx < arity; varIdx++) {
//            monitors[varIdx].freeze();
//            int numDeltaSize = monitors[varIdx].sizeApproximation();
//            if (numDeltaSize != 0) {
//                // 变量发生改变
//                deletedValues[varIdx].clear();
//                triggeringVars.add(varIdx);
//                // 只动变量论域改变的变量，触发变量和删值队列都更新一下
//                monitors[varIdx].forEachRemVal(onValRem.set(varIdx));
//                RD[varIdx].generateBitSet(D[varIdx]);
//                updatedVars.add(varIdx);
//            }
//            monitors[varIdx].unfreeze();
//        }
//    }
//
//    private boolean BandDCheck() {
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
//                int valIdx = val2Idx.get(j);
//                if (!D[i].get(valIdx)) {
//                    System.out.println("D[" + i + "] no contain but var: " + v.getName() + " contain:" + valIdx);
//                    return false;
//                }
//            }
//
//            for (int j = D[i].nextSetBit(0); j >= 0; j = D[i].nextSetBit(j + 1)) {
//                if (!v.contains(idx2Val[j])) {
//                    System.out.println("D[" + i + "] contain but var: " + v.getName() + "don't contain:" + j);
//                    return false;
//                }
//            }
//        }
//
//        return true;
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
//            updateBitDom(node);
////            needVisitValues.setAfterAnd(D[node], unVisitedValues);
////            for (int valIdx = needVisitValues.firstSetBit(); valIdx != unVisitedValues.end(); valIdx = needVisitValues.nextSetBit(valIdx + 1)) {
//            for (int valIdx = D[node].nextSetBit(0); valIdx >= 0; valIdx = D[node].nextSetBit(valIdx + 1)) {
//                if (visitedValues.get(valIdx)) continue;
//                visitedValues.set(valIdx);
//                updateBitBel(valIdx);
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
////                    freeNode.clear(valIdx);
//                    freeNode.remove(valIdx);
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
////                    freeNode.clear(valIdx);
//                    freeNode.remove(valIdx);
//                    matchedValuesR.set(valIdx);
//                }
//            }
//        }
//    }
//
//    private void findMaximumMatching() throws ContradictionException {
////        // !! 可做增量
//        freeNode.fill();
//        for (int varIdx = 0; varIdx < arity; varIdx++) {
//            if (var2ValR[varIdx].get() == -1) {
//                visitedValues.clear();
//                unVisitedVariables.set(0, arity);
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
//
////    protected void prepareForMatching() {
////        //freeNode.fill();
////        matchedValues.clear();
////        varsTmp.clear();
////        // 增量检查
////        // matching 有效性检查
////        for (int varIdx = 0; varIdx < arity; varIdx++) {
////            IntVar v = vars[varIdx];
////            // !! 这里可以修改一下 已赋值 就不参与修改了
////            if (v.getDomainSize() == 1) {
////                // 取出变量的唯一值
////                int valIdx = val2Idx.get(v.getValue());
////
////                int oldValIdx = var2Val[varIdx];
////                int oldVarIdx = val2Var[valIdx];
////
////                if (oldValIdx != -1 && oldValIdx != valIdx) {
////                    val2Var[oldValIdx] = -1;
////                }
////                if (oldVarIdx != -1 && oldVarIdx != varIdx) {
////                    var2Val[oldVarIdx] = -1;
////                }
////
////                val2Var[valIdx] = varIdx;
////                var2Val[varIdx] = valIdx;
////                //freeNode.remove(valIdx);
////                matchedValues.set(valIdx);
////            } else {
////                // 检查原匹配是否失效
////                int oldMatchingIndex = var2Val[varIdx];
////                if (oldMatchingIndex != -1) {
////                    // 如果oldMatchingValue无效
////                    if (!v.contains(idx2Val[oldMatchingIndex])) {
////                        val2Var[oldMatchingIndex] = -1;
////                        var2Val[varIdx] = -1;
////                        varsTmp.add(varIdx);
////                    } else {
////                        //freeNode.remove(oldMatchingIndex);
////                        matchedValues.set(oldMatchingIndex);
////                    }
////                } else {
////                    varsTmp.add(varIdx);
////                }
////
////            }
////        }
////    }
//
//    protected void repairMatching(int SCCStartIndex) throws ContradictionException {
//        // repair max matching.
//        partition.setIteratorIndexBySCCStartIndex(SCCStartIndex);
//        while (partition.hasNext()) {
//            int varIdx = partition.next();
//            updateBitDom(varIdx);
//            int valIdx = var2ValR[varIdx].get();
//            // 值失效
//            if (valIdx == -1 || !D[varIdx].get(valIdx)) {
//                var2ValR[varIdx].set(-1);
//                visitedValues.clear();
//                unVisitedVariables.set(0, arity);
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
//    protected void CheckAndRepairMatching() throws ContradictionException {
//        varsTmp.iterateValid();
//        while (varsTmp.hasNextValid()) {
//            int varIdx = varsTmp.next();
//            if (var2ValR[varIdx].get() == -1) {
//                visitedValues.clear();
////                visitedVariables.clear();
//                unVisitedVariables.set(0, arity);
//                MakeAugmentingPath(varIdx);
//            }
//            if (var2ValR[varIdx].get() == -1) {
//                // No augmenting path exists.
////                System.out.println("match fail");
////                for (int i = 0; i < vars.length; i++) {
////                    monitors[i].unfreeze();
////                }
////                    System.out.println("match fail");
////                Measurer.matchingTime += System.nanoTime() - startTime;
//                vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
//            }
//        }
//    }
//
//    protected boolean propagate_SCC_Match() throws ContradictionException {
//        boolean res = false;
//        IntVar x, y;
//        // 匹配值清空
//
////        prepareForMatching();
//        changedSCCStartIndex.clear();
//        System.out.println(partition);
//        triggeringVars.iterateValid();
//        while (triggeringVars.hasNextValid()) {
//            int xIdx = triggeringVars.next();
//            updateBitDom(xIdx);
////            int valIdx = var2Val[xIdx];
//            int valIdx = var2ValR[xIdx].get();
//
//            int sccStartIdx = partition.getSCCStartIndexByElement(xIdx);
//            x = vars[xIdx];
//
//            // valIdx失效
//            if (valIdx == -1 || !D[xIdx].get(valIdx)) {
//                repairMatching(sccStartIdx);
//            }
//
//            if (x.isInstantiated() && !partition.isSingletonByStartIndex(sccStartIdx)) {
//                valIdx = var2ValR[xIdx].get();
////                updateBitBel(valIdx);
//                updateBitBel(valIdx);
//                int xVal = idx2Val[valIdx];
//                if (changedSCCStartIndex.contains(sccStartIdx)) {
//                    changedSCCStartIndex.remove(sccStartIdx);
//                }
//
//                //parition s into s1 s2 , from now on s = s2
////                System.out.println("partition remove: " + xIdx + " " + (val2Idx.get(xVal) + addArity));
////                System.out.println(partition);
//                partition.remove(xIdx);
//                System.out.println(xIdx + " is isInstantiated to: " + xVal);
//                System.out.println(partition);
//
//                partition.setIteratorIndexBySCCStartIndex(sccStartIdx);
//                while (partition.hasNext()) {
//                    int yIdx = partition.next();
//                    updateBitDom(yIdx);
//                    if (D[yIdx].get(valIdx)) {
//                        System.out.println("remove: " + yIdx + ", " + xVal);
//                        y = vars[yIdx];
//                        res |= y.removeValue(xVal, aCause);
//                        removeValue(yIdx, valIdx);
//                        deletedValues[yIdx].add(valIdx);
//                    }
//                }
//
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
////        CheckAndRepairMatching();
//        return res;
//    }
//
////    protected void prepareForMatching() {
////        //freeNode.fill();
//////        matchedValues.clear();
//////        varsTmp.clear();
////        // 增量检查
////        // matching 有效性检查
////        triggeringVars.iterateValid();
////        while (triggeringVars.hasNextValid()) {
//////        for (int varIdx = 0; varIdx < arity; varIdx++) {
////            int varIdx = triggeringVars.next();
////            updateBitDom(varIdx);
//////            IntVar v = vars[varIdx];
////            // !! 这里可以修改一下 已赋值 就不参与修改了
////            if (D[varIdx].size() == 1) {
////                // 取出变量的唯一值
////                int valIdx = D[varIdx].nextSetBit(0);
////                updateBitBel(valIdx);
////                int oldValIdx = var2ValR[varIdx].get();
////                int oldVarIdx = val2VarR[valIdx].get();
////
////                if (oldValIdx != -1 && oldValIdx != valIdx) {
////                    val2VarR[oldValIdx].set(-1);
////                    updateBitBel(oldValIdx);
////                }
////                if (oldVarIdx != -1 && oldVarIdx != varIdx) {
////                    var2ValR[oldVarIdx].set(-1);
////                    updateBitBel(oldVarIdx);
////                }
////
////                val2VarR[valIdx].set(varIdx);
////                var2ValR[varIdx].set(valIdx);
////                //freeNode.remove(valIdx);
////                matchedValues.set(valIdx);
////                if (oldValIdx != -1) {
////                    matchedValues.clear(oldValIdx);
////                }
////            } else {
////                // 检查原匹配是否失效
////                int oldMatchingIndex = var2ValR[varIdx].get();
////                if (oldMatchingIndex != -1) {
////                    // 如果oldMatchingValue无效
////                    if (!D[varIdx].get(oldMatchingIndex)) {
//////                    if (!D[varIdx].get(oldMatchingIndex)) {
////                        val2VarR[oldMatchingIndex].set(-1);
//////                        unMatchedValues.set(oldMatchingIndex);
////                        matchedValues.clear(oldMatchingIndex);
//////                        matchedValues.set(oldMatchingIndex);
////                        var2ValR[varIdx].set(-1);
////                    } else {
//////                        //freeNode.clear(oldMatchingIndex);
////                        //freeNode.remove(oldMatchingIndex);
////                        matchedValues.set(oldMatchingIndex);
//////                    System.out.println(oldMatchingIndex + " is free");
////                    }
////                }
////
////            }
////        }
////    }
//
//    protected boolean propagate_SCC_filter() throws ContradictionException {
////        distinguish();
////        initiateMatrix();
//        boolean filter = false;
////        unconnected = false;
////        unconnected = !gammaMask.isEmpty();
//        changedSCCStartIndex.iterateValid();
//        while (changedSCCStartIndex.hasNextValid()) {
//            int sccStartIndex = changedSCCStartIndex.next();
////            partition.getPartitionVars(sccStartIndex, varsTmp);
////            partition.setIteratorIndexBySCCStartIndex(sccStartIndex);
//            initiateMatrix(sccStartIndex);
//
//            filter |= filterDomains(sccStartIndex);
//
////            partition.getPartitionBitSetMaskAndVars(sccStartIndex, restriction, varsTmp, notGamma, valsTmp, notA, freeNodes, arity, numNodes);
////            resetData(varsTmp, valsTmp, restriction.get(arity));
////            if (freeNodes.validSize() != 0) {
////                propagateFreeNodes();
////            }
//////            System.out.println("valDFSNum: " + Arrays.toString(valDFSNum) + ", " + restriction + "," + partition);
////            findAllSCC(restriction, varsTmp);
////            filter |= filterDomains(varsTmp, valsTmp);
//        }
//        return filter;
//    }
//    //***********************************************************************************
//    // PRUNING
//    //***********************************************************************************
//
//
//    private void distinguish() {
//        notGamma.fill();
//        notA.fill();
//        gammaMask.clear();
//
//        freeNode.iterateValid();
//        while (freeNode.hasNextValid()) {
//            // 每个freeNode的值拿出来
////            System.out.println(i);
//            int valIdx = freeNode.next();
//            notA.remove(valIdx);
//            gammaMask.or(B[valIdx]);
//        }
//        gammaFrontier.set(gammaMask);
//
//        for (int varIdx = gammaFrontier.nextSetBit(0);
//             varIdx >= 0; varIdx = gammaFrontier.nextSetBit(0)) {
//            // !! 这里可以将Extended改成Frontier，只记录前沿，记录方法是三个BitSet比较，
//            // frontier 扩展，从valMask中去掉gammaMask已记录的变量
//            int valIdx = var2ValR[varIdx].get();
//            gammaFrontier.orAfterMinus(B[valIdx], gammaMask);
////            // 除去第i个变量
//            gammaFrontier.clear(varIdx);
//            // gamma 扩展
//            gammaMask.or(B[valIdx]);
//            notGamma.remove(varIdx);
//            notA.remove(valIdx);
//        }
//
//    }
//
//    private void initiateMatrix() {
//        // 重置两个矩阵
//        // 只重置notGamma的变量
//        notGamma.iterateValid();
//        while (notGamma.hasNextValid()) {
//            int varIdx = notGamma.next();
//            // 从变量id拿到匹配值再拿到该值所能到达的变量mask
//            if (!vars[varIdx].isInstantiated()) {
//                graphLinkedMatrix[varIdx].setAfterMinus(B[var2ValR[varIdx].get()], gammaMask);
//                graphLinkedMatrix[varIdx].clear(varIdx);
//                graphLinkedFrontier[varIdx].set(graphLinkedMatrix[varIdx]);
//            }
////                System.out.println("------graphLinkedMatrix[" + varIdx + "]------");
////                System.out.println(graphLinkedMatrix[varIdx]);
////                System.out.println(graphLinkedFrontier[varIdx]);
//        }
//    }
//
//    private void initiateMatrix(int sccStartIdx) {
//        // 重置两个矩阵
//        // 只重置notGamma的变量
//        partition.setIteratorIndexBySCCStartIndex(sccStartIdx);
//        while (partition.hasNext()) {
//
//            int varIdx = partition.next();
//            updateBitDom(varIdx);
//            // 从变量id拿到匹配值再拿到该值所能到达的变量mask
////            if (!vars[varIdx].isInstantiated()) {
//            int valIdx = var2ValR[varIdx].get();
//            updateBitBel(valIdx);
//            graphLinkedMatrix[varIdx].set(B[valIdx]);
////                graphLinkedMatrix[varIdx].setAfterMinus(B[valIdx], gammaMask);
//            graphLinkedMatrix[varIdx].clear(varIdx);
//            graphLinkedFrontier[varIdx].set(graphLinkedMatrix[varIdx]);
////            }
//            System.out.println("------graphLinkedMatrix[" + varIdx + "]------");
//            System.out.println(graphLinkedMatrix[varIdx]);
//            System.out.println(graphLinkedFrontier[varIdx]);
//        }
//
//    }
//
////    private boolean filter() throws ContradictionException {
////        distinguish();
////        initiateMatrix();
////        // 这里判断一下，如果notGamma为空则不用进行如下步骤
////        boolean filter = false;
////        for (int varIdx = 0; varIdx < arity; varIdx++) {
////            IntVar v = vars[varIdx];
////            if (!v.isInstantiated()) {
////                for (int valIdx = D[varIdx].nextSetBit(0); valIdx >= 0; valIdx = D[varIdx].nextSetBit(valIdx + 1)) {
////                    int k = idx2Val[valIdx];
//////                    System.out.println(valIdx);
////                    if (!notGamma.contains(varIdx) && notA.contains(valIdx)) {
////                        ++Measurer.numDelValuesP1;
////                        Measurer.enterP1();
//////                        D[varIdx].clear(valIdx);
////                        filter |= v.removeValue(k, aCause);
////                        removeValue(varIdx, valIdx);
////                        System.out.println("first delete: " + v.getName() + ", " + k);
////                    } else if (notGamma.contains(varIdx) && notA.contains(valIdx)) {
////                        if (!checkSCC(varIdx, valIdx)) {
////                            Measurer.enterP2();
////                            if (valIdx == var2ValR[varIdx].get()) {
////                                int valNum = v.getDomainSize();
////                                Measurer.numDelValuesP2 += valNum - 1;
////                                filter |= v.instantiateTo(k, aCause);
////                                instantiateTo(varIdx, valIdx);
//////                            System.out.println("instantiate  : " + v.getName() + ", " + k);
////                            } else {
////                                ++Measurer.numDelValuesP2;
////                                filter |= v.removeValue(k, aCause);
////                                removeValue(varIdx, valIdx);
////                                System.out.println("second delete: " + v.getName() + ", " + k);
////                            }
////                        }
////                    }
////                }
////            }
////        }
////        return filter;
////    }
//
////    private boolean filterDomains(int sccStartIndex, SparseSet filterVars) throws ContradictionException {
////        boolean filter = false;
////        filterVars.iterateValid();
////        while (filterVars.hasNextValid()) {
////            int varIdx = filterVars.next();
////            IntVar v = vars[varIdx];
////            if (!v.isInstantiated()) {
////                for (int valIdx = D[varIdx].nextSetBit(0); valIdx >= 0; valIdx = D[varIdx].nextSetBit(valIdx + 1)) {
////                    int k = idx2Val[valIdx];
////                    int varIdx2 = val2VarR[valIdx].get();
//////                    System.out.println(valIdx);
////                    if (!notGamma.contains(varIdx) && notA.contains(valIdx)) {
////                        ++Measurer.numDelValuesP1;
////                        Measurer.enterP1();
////                        filter |= v.removeValue(k, aCause);
////                        removeValue(varIdx, valIdx);
////                        //                System.out.println("first delete: " + v.getName() + ", " + k);
////                    } else if (notGamma.contains(varIdx) && notA.contains(valIdx)) {
////                        if (!checkSCC(varIdx, valIdx)) {
////                            Measurer.enterP2();
////                            if (valIdx == var2ValR[varIdx].get()) {
////                                int valNum = v.getDomainSize();
////                                Measurer.numDelValuesP2 += valNum - 1;
////                                filter |= v.instantiateTo(k, aCause);
////                                instantiateTo(varIdx, valIdx);
//////                            System.out.println("instantiate  : " + v.getName() + ", " + k);
////                            } else {
////                                ++Measurer.numDelValuesP2;
////                                filter |= v.removeValue(k, aCause);
////                                removeValue(varIdx, valIdx);
//////                            System.out.println("second delete: " + v.getName() + ", " + k);
////                            }
////                        }
//////                        else if (graphLinkedMatrix[varIdx2].get(varIdx)) {
//////                            sccMatrix[varIdx].set(varIdx2);
//////                            sccMatrix[varIdx2].set(valIdx);
//////                        }
////                    }
////                }
////            }
////        }
////
//////        // 装填SCC
//////        partition.setIteratorIndexBySCCStartIndex(sccStartIndex);
//////        filterVars.iterateValid();
//////        while (filterVars.hasNextValid()) {
//////            int x = filterVars.next();
//////            partition.add(x);
//////            for (int y = sccMatrix[x].nextSetBit(0); y != -1; y = sccMatrix[x].nextSetBit(y + 1)) {
//////                filterVars.remove(y);
//////                partition.add(y);
//////            }
//////            partition.setSplit();
//////
//////            if (filterVars.contains(x))
//////                filterVars.remove();
//////        }
////        return filter;
////    }
//
//    private boolean filterDomains(int sccStartIndex) throws ContradictionException {
//        boolean filter = false;
////        filterVars.iterateValid();
////        while (filterVars.hasNextValid()) {
////            int varIdx = filterVars.next();
//        partition.setIteratorIndexBySCCStartIndex(sccStartIndex);
//        while (partition.hasNext()) {
//            int varIdx = partition.nextAndSplitWhenMeetingUnknownAndMoved();
//            IntVar v = vars[varIdx];
//            if (!v.isInstantiated()) {
//                for (int valIdx = D[varIdx].nextSetBit(0); valIdx >= 0; valIdx = D[varIdx].nextSetBit(valIdx + 1)) {
//                    int k = idx2Val[valIdx];
//
//                    if (!checkSCC(varIdx, valIdx)) {
//                        Measurer.enterP2();
//                        int varIdx2 = val2VarR[valIdx].get();
//                        if (varIdx == varIdx2) {
//                            int valNum = v.getDomainSize();
//                            Measurer.numDelValuesP2 += valNum - 1;
//                            filter |= v.instantiateTo(k, aCause);
//                            instantiateTo(varIdx, valIdx);
//                            partition.removeCurrentToTail();
//                            System.out.println("instantiate  : " + v.getName() + ", " + k);
//                        } else {
//                            ++Measurer.numDelValuesP2;
//                            filter |= v.removeValue(k, aCause);
//                            removeValue(varIdx, valIdx);
//                            if (partition.canMove(varIdx2)) {
//                                // varIdx2未分裂，将varIdx2移入tmp分区中
//                                partition.addMoved(varIdx2);
//                            }
//                            System.out.println("second delete: " + v.getName() + ", " + k);
//                        }
//                    }
//////                    System.out.println(valIdx);
////                    if (!notGamma.contains(varIdx) && notA.contains(valIdx)) {
////                        ++Measurer.numDelValuesP1;
////                        Measurer.enterP1();
////                        filter |= v.removeValue(k, aCause);
////                        removeValue(varIdx, valIdx);
////                        //                System.out.println("first delete: " + v.getName() + ", " + k);
////                    } else if (notGamma.contains(varIdx) && notA.contains(valIdx)) {
////                        if (!checkSCC(varIdx, valIdx)) {
////                            Measurer.enterP2();
////                            if (valIdx == var2ValR[varIdx].get()) {
////                                int valNum = v.getDomainSize();
////                                Measurer.numDelValuesP2 += valNum - 1;
////                                filter |= v.instantiateTo(k, aCause);
////                                instantiateTo(varIdx, valIdx);
//////                            System.out.println("instantiate  : " + v.getName() + ", " + k);
////                            } else {
////                                ++Measurer.numDelValuesP2;
////                                filter |= v.removeValue(k, aCause);
////                                removeValue(varIdx, valIdx);
//////                            System.out.println("second delete: " + v.getName() + ", " + k);
////                            }
////                        }
//////                        else if (graphLinkedMatrix[varIdx2].get(varIdx)) {
//////                            sccMatrix[varIdx].set(varIdx2);
//////                            sccMatrix[varIdx2].set(valIdx);
//////                        }
////                    }
//                }
//            }
//        }
//        partition.disposeSCCIterator();
////        // 装填SCC
////        partition.setIteratorIndexBySCCStartIndex(sccStartIndex);
////        filterVars.iterateValid();
////        while (filterVars.hasNextValid()) {
////            int x = filterVars.next();
////            partition.add(x);
////            for (int y = sccMatrix[x].nextSetBit(0); y != -1; y = sccMatrix[x].nextSetBit(y + 1)) {
////                filterVars.remove(y);
////                partition.add(y);
////            }
////            partition.setSplit();
////
////            if (filterVars.contains(x))
////                filterVars.remove();
////        }
//        return filter;
//    }
//
//
//    private boolean checkSCC(int x, int a) {
////        System.out.println("check:" + varIdx + ", " + valIdx);
//        // 若没有 就需要BFS一下Frontier没有，就表示不用扩展了
//        // 注意一下return退出时frontier正确
//        // 确保x<y
//        int y = val2VarR[a].get();
////        int y;
////        if (x <= val2Var[a]) {
////            y = val2Var[a];
////        } else {
////            y = x;
////            x = val2Var[a];
////        }
//        if (graphLinkedMatrix[x].get(y)) {
//            return true;
//        }
//        for (int i = graphLinkedFrontier[x].nextSetBit(0);
//             i >= 0; i = graphLinkedFrontier[x].nextSetBit(0)) {
//            // frontier扩张，除掉变量i 因为变量i已被扩展。
//            graphLinkedFrontier[x].orAfterMinus(graphLinkedMatrix[i], graphLinkedMatrix[x]);
//            graphLinkedFrontier[x].clear(i);
//            graphLinkedMatrix[x].or(graphLinkedMatrix[i]);
//            if (graphLinkedMatrix[x].get(y)) {
//                return true;
//            }
//        }
//        return false;
//    }
//
//    void removeValue(int varIdx, int valIdx) {
//        D[varIdx].clear(valIdx);
//        RD[varIdx].clear(valIdx);
//        B[valIdx].clear(varIdx);
//        RB[valIdx].clear(varIdx);
//    }
//
//    void instantiateTo(int varIdx, int valIdx) {
//        D[varIdx].clear();
//        RD[varIdx].clear();
//        D[varIdx].set(valIdx);
//        RD[varIdx].set(valIdx);
//
//        B[valIdx].clear();
//        RB[valIdx].clear();
//        B[valIdx].set(varIdx);
//        RB[valIdx].set(varIdx);
//    }
//
//
//    // for lazy update, 最早在matching时，最晚在initiateMatrix时检测
//    void updateBitBel(int valIdx) {
//        // bit值未更新，此处更新
//        if (!updatedVals.contains(valIdx)) {
//            updatedVals.add(valIdx);
//            System.out.println("RB[" + valIdx + "]\t" + RB[valIdx]);
//            RB[valIdx].generateBitSet(B[valIdx]);
//            System.out.println("B[" + valIdx + "]\t" + B[valIdx]);
//        }
//    }
//
//    // for lazy update, 最早在matching时，最晚在initiateMatrix时检测
//    void updateBitDom(int varIdx) {
//        // bit值未更新，此处更新
//        if (!updatedVars.contains(varIdx)) {
//            updatedVars.add(varIdx);
//            System.out.println("RD[" + varIdx + "]\t" + RD[varIdx]);
//            RD[varIdx].generateBitSet(D[varIdx]);
//            System.out.println("D[" + varIdx + "]\t" + D[varIdx]);
//        }
//    }
//}
////
////
////    private void deltaUpdate() throws ContradictionException {
////        // 触发队列和更新队列
////        triggeringVars.clear();
////        triggeringVals.clear();
////        updatedVars.clear();
////        updatedVals.clear();
//////        lastBindVar = INDEX_OVERFLOW;
////
////        for (int varIdx = 0; varIdx < arity; varIdx++) {
////            monitors[varIdx].freeze();
////            int numDeltaSize = monitors[varIdx].sizeApproximation();
////            if (numDeltaSize != 0) {
////                // 变量发生改变
////                deletedValues[varIdx].clear();
////                triggeringVars.add(varIdx);
////                // 只动变量论域改变的变量，触发变量和删值队列都更新一下
//////                IntVar v = vars[varIdx];
////                monitors[varIdx].forEachRemVal(onValRem.set(varIdx));
//////                    D[varIdx].set(RD[varIdx]);
////                RD[varIdx].generateBitSet(D[varIdx]);
////                updatedVars.add(varIdx);
//////                if (v.isInstantiated()) {
//////                    // 变量刚刚被赋值
//////                    if (lastBindVar != INDEX_OVERFLOW)
//////                        System.out.println("error: multi bind");
//////                    lastBindVar = varIdx;
//////                    int valIdx = domIsRegular[varIdx] ? vars[varIdx].getValue() : val2Idx.get(vars[varIdx].getValue());
//////                    fillBitDBAfterInst(varIdx, valIdx);
//////                    updatedVars.add(varIdx);
////////                    updatedVals.add(valIdx);
//////                    triggeringVals.add(valIdx);
//////                } else {
//////                    // 否则更新
//////                    monitors[varIdx].forEachRemVal(onValRem.set(varIdx));
////////                    D[varIdx].set(RD[varIdx]);
//////                    RD[varIdx].generateBitSet(D[varIdx]);
//////                    updatedVars.add(varIdx);
//////                }
////            }
////            monitors[varIdx].unfreeze();
////        }
////    }
//package org.chocosolver.solver.constraints.nary.alldifferent.algo;
//
////import org.chocosolver.amtf.Measurer;
//
//import gnu.trove.iterator.TIntIntIterator;
//import gnu.trove.map.hash.TIntIntHashMap;
//import org.chocosolver.memory.IEnvironment;
//import org.chocosolver.memory.IStateBitSet;
//import org.chocosolver.memory.IStateInt;
//import org.chocosolver.solver.ICause;
//import org.chocosolver.solver.Model;
//import org.chocosolver.solver.exception.ContradictionException;
//import org.chocosolver.solver.variables.IntVar;
//import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
//import org.chocosolver.util.iterators.DisposableValueIterator;
//import org.chocosolver.util.objects.IStateBitSetPartition;
//import org.chocosolver.util.objects.Measurer;
//import org.chocosolver.util.objects.SimpleBitSet;
//import org.chocosolver.util.objects.SparseSet;
//import org.chocosolver.util.procedure.UnaryIntProcedure;
//
//import java.util.Arrays;
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
//public class AlgoAllDiffAC_SimpleGentDebug extends AlgoAllDiffAC_Simple {
//
//    //***********************************************************************************
//    // VARIABLES
//    //***********************************************************************************
//    // 约束的个数
//    static public int num = 0;
//    static public int INDEX_OVERFLOW = -1;
//    static long numCall =-1;
//    // 约束的编号
//    private int id;
//    private int arity;
//    private IntVar[] vars;
//    private ICause aCause;
//    // 新增一点（视为变量）
////    private int addArity;
//    // 自由值集合
//    private SparseSet freeNode;
//    // 以下是bit版本所需数据结构========================
//    // numValue是二部图中取值编号的个数，numBit是二部图的最大边数
//    private int numValues;
//    // 值到索引
//    private int[] idx2Val;
//    // 索引到值
//    private TIntIntHashMap val2Idx;
//    // Xc-Γ(A)
//    private SparseSet notGamma;
//    // Dc-A
//    private SparseSet notA;
//    // 与值相连的变量
//    private SimpleBitSet[] B;
//    private SimpleBitSet[] D;
//
//    // 已访问过的变量和值
////    private SimpleBitSet visitedVariables;
//    private SimpleBitSet unVisitedVariables;
//    //    private SimpleBitSet value_visited_;
////    private SimpleBitSet unVisitedValues;
////    private SimpleBitSet needVisitValues;
//    private BitSet visitedValues;
//    //    private SparseSet unVisitedValues;
//    //    private BitSet needVisitValues;
//    //    private SimpleBitSet unMatchedValues;
////    private SimpleBitSet matchedValues;
//    private IStateBitSet matchedValuesR;
//    private SimpleBitSet freeNodes;
//    //    private SimpleBitSet matchedMasks;
////    private SimpleBitSet varSingletonMask;
////    private SimpleBitSet valSingletonMask;
////    private SimpleBitSet varTmpMask;
//    // matching
////    private int[] val2Var;
////    private int[] var2Val;
//    private IStateInt[] val2VarR;
//    private IStateInt[] var2ValR;
//    // 记录队列
//    private int[] visiting_;
//    private int[] variable_visited_from_;
//
//    // 变量到变量的连通性
//    // 对于惰性算法，记录是否知道-变量到变量的连通性
//    private SimpleBitSet[] graphLinkedMatrix;
//    private SimpleBitSet[] graphLinkedFrontier;
//
//    // !! 记录gamma的前沿
//    private SimpleBitSet gammaFrontier;
//    // 记录gamma的bitset
//    private SimpleBitSet gammaMask;
//
//    // 记录scc
////    private BitSet[] sccMatrix;
//    protected boolean initialPropagation = true;
//    //    protected RSetPartition partition;
////    protected RSetPartition partition;
//    protected IStateBitSetPartition partition;
//    private SparseSet triggeringVars;
//    //    private SparseSet triggeringVals;
//    private IIntDeltaMonitor[] monitors;
//    private UnaryIntProcedure<Integer> onValRem;
//    private SparseSet[] deletedValues;
//    protected SparseSet varsTmp;
//    private SparseSet changedSCCStartIndex;
//    protected boolean unconnected = false;
//    protected boolean isSkiped = false;
//
//    // 懒计算域更新
//    private SparseSet updatedVars;
//    private SparseSet updatedVals;
//
//    long startTime;
//    private IEnvironment env;
//    //    private int endBitIndex = 64;
//    // for delta update
////    protected IIntDeltaMonitor[] monitors;
////    private UnaryIntProcedure<Integer> onValRem;
////    private boolean initialProp = true;
////
////    //    // for backtrack
////    IEnvironment env;
//    IStateBitSet[] RB;
//    IStateBitSet[] RD;
//    // if all a in var x val2Idx[a] = a then DomIsRagular[x] = true
//    boolean[] domIsRegular;
//    int lastBindVar = INDEX_OVERFLOW;
//
//    //***********************************************************************************
//    // CONSTRUCTORS
//    //***********************************************************************************
//    public AlgoAllDiffAC_SimpleGentDebug(IntVar[] variables, ICause cause, Model model) {
//        super(variables, cause, model.getEnvironment());
//        id = num++;
//        env = model.getEnvironment();
//        vars = variables;
//        aCause = cause;
//        arity = vars.length;
//        val2Idx = new TIntIntHashMap();
//
//        // 先将从0开始的变量论域进行编码，只编一个变量
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            if (v.getLB() == 0) {
//                for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
//                    if (!val2Idx.containsKey(j)) {
//                        val2Idx.put(j, val2Idx.size());
//                    }
//                }
//                break;
//            }
//        }
//
//        // 全部从头编码
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
//                if (!val2Idx.containsKey(j)) {
//                    val2Idx.put(j, val2Idx.size());
//                }
//            }
//        }
//
//        numValues = val2Idx.size();
//        idx2Val = new int[numValues];
//        TIntIntIterator it = val2Idx.iterator();
//        while (it.hasNext()) {
//            it.advance();
//            idx2Val[it.value()] = it.key();
//        }
//
//        // System.out.println("-----------idx2Val-----------");
//        // System.out.println(Arrays.toString(idx2Val));
//        // for backtracking
//        B = new SimpleBitSet[numValues];
//        RB = new IStateBitSet[numValues];
//        for (int i = 0; i < numValues; ++i) {
//            B[i] = new SimpleBitSet(arity);
//            RB[i] = env.makeBitSet(arity);
//        }
//
//        D = new SimpleBitSet[arity];
//        RD = new IStateBitSet[arity];
//        domIsRegular = new boolean[arity];
//        for (int i = 0; i < arity; i++) {
//            D[i] = new SimpleBitSet(numValues);
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
//                B[valIdx].set(i);
//                RD[i].set(valIdx);
//                D[i].set(valIdx);
//            }
//            vit.dispose();
//        }
//
//        // 记录访问过的变量
//        visiting_ = new int[arity];
//        unVisitedVariables = new SimpleBitSet(arity);
//        // 变量的前驱变量，若前驱变量是-1，则表示无前驱变量，就是第一个变量
//        variable_visited_from_ = new int[arity];
//        visitedValues = new BitSet(numValues);
////        matchedValues = new SimpleBitSet(numValues);
//        matchedValuesR = env.makeBitSet(numValues);
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
//        freeNode = new SparseSet(numValues);
//        gammaFrontier = new SimpleBitSet(arity);
//        gammaMask = new SimpleBitSet(arity);
//        notGamma = new SparseSet(arity);
//        notA = new SparseSet(numValues);
//
//        graphLinkedMatrix = new SimpleBitSet[arity];
//        graphLinkedFrontier = new SimpleBitSet[arity];
//        for (int i = 0; i < arity; ++i) {
//            graphLinkedMatrix[i] = new SimpleBitSet(arity);
//            graphLinkedFrontier[i] = new SimpleBitSet(arity);
//        }
//
//        // for Gent algorithm
//        partition = new IStateBitSetPartition(arity, env);
//        triggeringVars = new SparseSet(arity);
////        triggeringVals = new SparseSet(numValues);
//        // 已懒更新的变量/值
//        updatedVars = new SparseSet(arity);
//        updatedVals = new SparseSet(numValues);
//        varsTmp = new SparseSet(arity);
//        changedSCCStartIndex = new SparseSet(arity);
//        monitors = new IIntDeltaMonitor[vars.length];
//        for (int i = 0; i < vars.length; i++) {
//            monitors[i] = vars[i].monitorDelta(cause);
//        }
//        onValRem = makeProcedure();
//
//        deletedValues = new SparseSet[arity];
//        for (int i = 0; i < arity; i++) {
//            deletedValues[i] = new SparseSet(numValues);
//        }
//    }
//
//    protected UnaryIntProcedure<Integer> makeProcedure() {
//        return new UnaryIntProcedure<Integer>() {
//            int varIdx;
//            IntVar v;
//            int matchedVal = -1;
//
//            @Override
//            public UnaryIntProcedure set(Integer o) {
//                varIdx = o;
//                v = vars[varIdx];
//                matchedVal = var2ValR[varIdx].get();
//                return this;
//            }
//
//            @Override
//            public void execute(int i) {
////                if (!triggeringVars.contains(var)) {
////                    triggeringVars.add(var);
////                    deletedValues[var].clear();
////                }
//                int valIdx = domIsRegular[varIdx] ? i : val2Idx.get(i);
////                if (!triggeringVals.contains(valIdx)) {
////                    triggeringVals.add(valIdx);
////                }
//
//                // 删的值是匹配值，清理匹配
//                if (valIdx == matchedVal) {
//                    var2ValR[varIdx].set(-1);
//                    val2VarR[valIdx].set(-1);
//                    matchedValuesR.clear(valIdx);
//                }
//
//                deletedValues[varIdx].add(valIdx);
//                RB[valIdx].clear(varIdx);
//                RD[varIdx].clear(valIdx);
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
//        System.out.println("----------------" + id + " propagate: " + (++numCall) + "----------------");
//        printDomains();
//        boolean filter = false;
//        Measurer.enterProp();
//        System.out.println(partition);
//        if (initialPropagation) {
////            triggeringVals.fill();
//            triggeringVars.fill();
//            updatedVars.fill();
//            updatedVals.fill();
//
//            startTime = System.nanoTime();
//            findMaximumMatching();
//            Measurer.matchingTime += System.nanoTime() - startTime;
//
//            System.out.println("matching: " + Arrays.toString(var2ValR));
//
//            startTime = System.nanoTime();
//            initiateMatrix(0);
//            filter = filterDomains(0);
//            Measurer.filterTime += System.nanoTime() - startTime;
//
//            initialPropagation = false;
//        } else {
//
//            deltaUpdate();
//
//            startTime = System.nanoTime();
//            filter |= propagate_SCC_Match();
//            Measurer.matchingTime += System.nanoTime() - startTime;
//            System.out.println("matching: " + Arrays.toString(var2ValR));
//
//            startTime = System.nanoTime();
//            System.out.println("updvar:" + updatedVars);
//            System.out.println("updval:" + updatedVals);
//            filter |= propagate_SCC_filter();
//            System.out.println("updvar2:" + updatedVars);
//            System.out.println("updval2:" + updatedVals);
////            System.out.println(partition);
//            Measurer.filterTime += System.nanoTime() - startTime;
//        }
////        for (int i = 0; i < arity; i++) {
////            RD[i].getWord()
////        }
////        startTime = System.nanoTime();
////        findMaximumMatching();
////        Measurer.matchingTime += System.nanoTime() - startTime;
//
////        startTime = System.nanoTime();
////        filter = filter();
////        Measurer.filterTime += System.nanoTime() - startTime;
//        return filter;
//    }
//
//    //***********************************************************************************
//    // Initialization
//    //***********************************************************************************
//
//
////    protected UnaryIntProcedure<Integer> makeProcedure() {
////        return new UnaryIntProcedure<Integer>() {
////            int var;
////            int valIdx;
////
////            @Override
////            public UnaryIntProcedure set(Integer o) {
////                var = o;
////                return this;
////            }
////
////            @Override
////            public void execute(int i) throws ContradictionException {
//////                DE.push(new IntTuple2(var, val2Idx.get(i) + addArity));
//////                IntVar v = vars[var];
////                valIdx = val2Idx.get(i);
////                RD[var].clear(valIdx);
////                RB[valIdx].clear(var);
//////                System.out.println(vars[var].getName() + "," + var + ", " + i + " = " + v.contains(i) + ", size = " + v.getDomainSize());
////            }
////        };
////    }
//
//    private void printDomains() {
//        // 填充B和D
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            System.out.println(D[i]);
//            System.out.println(v);
//        }
//    }
//
//    private void printBitDomains() {
//        for (int i = 0; i < numValues; ++i) {
//            System.out.println("val " + "i: " + B[i]);
//        }
//
//        IntVar v;
//        // 填充B和D
//        for (int i = 0; i < arity; ++i) {
//            v = vars[i];
//            System.out.println("val " + "i: " + D[i]);
//            System.out.println(v);
//        }
//    }
//
//
//    // 都不要了，改成懒计算。
//    private void fillBAndD(SparseSet changedVars, SparseSet changedVals) {
//        // 应该大范围更新
//        changedVars.iterateValid();
//        while (changedVars.hasNextValid()) {
//            int v = changedVars.next();
//            RD[v].generateBitSet(D[v]);
//            updatedVars.add(v);
//        }
//
//        changedVals.iterateValid();
//        while (changedVals.hasNextValid()) {
//            int a = changedVals.next();
//            RB[a].generateBitSet(B[a]);
//            updatedVals.add(a);
//        }
//    }
//
//    // 初始化RB和RD填充B和D
//    private void initialBDRBAndRD() {
//        // 填充B和D
//        for (int i = 0; i < numValues; ++i) {
//            B[i].clear();
//            RB[i].clear();
//        }
//
//        for (int i = 0; i < arity; ++i) {
//            D[i].clear();
//            RD[i].clear();
//            IntVar v = vars[i];
//            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
//                int valIdx = domIsRegular[i] ? j : val2Idx.get(j);
//                D[i].set(valIdx);
//                RD[i].set(valIdx);
//                B[valIdx].set(i);
//                RB[valIdx].set(i);
//            }
//        }
//    }
//
//    private void fill(int varIdx) {
//        // 填充RB和RD
////        for (int i = 0; i < arity; ++i) {
//        RD[varIdx].clear();
//        IntVar v = vars[varIdx];
//        if (domIsRegular[varIdx]) {
//            for (int i = v.getLB(), ub = v.getUB(); i <= ub; i = v.nextValue(i)) {
//                RD[varIdx].set(i);
//            }
//        } else {
//            for (int i = v.getLB(), ub = v.getUB(); i <= ub; i = v.nextValue(i)) {
//                RD[varIdx].set(val2Idx.get(i));
//            }
//        }
//
//    }
//
//    private void fillBitDBAfterInst(int varIdx, int valIdx) throws ContradictionException {
//        // 只在变量varIdx赋值后调用
//        D[varIdx].clear();
//        RD[varIdx].clear();
//        D[varIdx].set(valIdx);
//        RD[varIdx].set(valIdx);
//
//        // valIdx赋值的变量论域中都除去
//        for (int yIdx = RB[valIdx].nextSetBit(0); yIdx > 0; yIdx = RB[valIdx].nextSetBit(yIdx + 1)) {
//            if (yIdx != varIdx) {
////                updateBitDom(yIdx);
//                System.out.println("remove: " + yIdx + ", " + valIdx);
//                IntVar y = vars[yIdx];
//                int xVal = idx2Val[varIdx];
//                boolean res = y.removeValue(xVal, aCause);
//                removeValue(yIdx, valIdx);
//                deletedValues[yIdx].add(valIdx);
//            }
//        }
//    }
//
//    private void deltaUpdate() throws ContradictionException {
//        // 触发队列和更新队列
//        triggeringVars.clear();
////        triggeringVals.clear();
//        updatedVars.clear();
//        updatedVals.clear();
////        matchedValues.clear();
////        lastBindVar = INDEX_OVERFLOW;
//
//        for (int varIdx = 0; varIdx < arity; varIdx++) {
//            monitors[varIdx].freeze();
//            int numDeltaSize = monitors[varIdx].sizeApproximation();
//            if (numDeltaSize != 0) {
//                // 变量发生改变
//                deletedValues[varIdx].clear();
//                triggeringVars.add(varIdx);
//                // 只动变量论域改变的变量，触发变量和删值队列都更新一下
//                monitors[varIdx].forEachRemVal(onValRem.set(varIdx));
//                RD[varIdx].generateBitSet(D[varIdx]);
//                updatedVars.add(varIdx);
//            }
//            monitors[varIdx].unfreeze();
//        }
//    }
//
//    private boolean BandDCheck() {
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
//                int valIdx = val2Idx.get(j);
//                if (!D[i].get(valIdx)) {
//                    System.out.println("D[" + i + "] no contain but var: " + v.getName() + " contain:" + valIdx);
//                    return false;
//                }
//            }
//
//            for (int j = D[i].nextSetBit(0); j >= 0; j = D[i].nextSetBit(j + 1)) {
//                if (!v.contains(idx2Val[j])) {
//                    System.out.println("D[" + i + "] contain but var: " + v.getName() + "don't contain:" + j);
//                    return false;
//                }
//            }
//        }
//
//        return true;
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
//            updateBitDom(node);
////            needVisitValues.setAfterAnd(D[node], unVisitedValues);
////            for (int valIdx = needVisitValues.firstSetBit(); valIdx != unVisitedValues.end(); valIdx = needVisitValues.nextSetBit(valIdx + 1)) {
//            for (int valIdx = D[node].nextSetBit(0); valIdx >= 0; valIdx = D[node].nextSetBit(valIdx + 1)) {
//                if (visitedValues.get(valIdx)) continue;
//                visitedValues.set(valIdx);
//                updateBitBel(valIdx);
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
////                    freeNode.clear(valIdx);
//                    freeNode.remove(valIdx);
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
////                    freeNode.clear(valIdx);
//                    freeNode.remove(valIdx);
//                    matchedValuesR.set(valIdx);
//                }
//            }
//        }
//    }
//
//    private void findMaximumMatching() throws ContradictionException {
////        // !! 可做增量
//        freeNode.fill();
//        for (int varIdx = 0; varIdx < arity; varIdx++) {
//            if (var2ValR[varIdx].get() == -1) {
//                visitedValues.clear();
//                unVisitedVariables.set(0, arity);
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
//
////    protected void prepareForMatching() {
////        //freeNode.fill();
////        matchedValues.clear();
////        varsTmp.clear();
////        // 增量检查
////        // matching 有效性检查
////        for (int varIdx = 0; varIdx < arity; varIdx++) {
////            IntVar v = vars[varIdx];
////            // !! 这里可以修改一下 已赋值 就不参与修改了
////            if (v.getDomainSize() == 1) {
////                // 取出变量的唯一值
////                int valIdx = val2Idx.get(v.getValue());
////
////                int oldValIdx = var2Val[varIdx];
////                int oldVarIdx = val2Var[valIdx];
////
////                if (oldValIdx != -1 && oldValIdx != valIdx) {
////                    val2Var[oldValIdx] = -1;
////                }
////                if (oldVarIdx != -1 && oldVarIdx != varIdx) {
////                    var2Val[oldVarIdx] = -1;
////                }
////
////                val2Var[valIdx] = varIdx;
////                var2Val[varIdx] = valIdx;
////                //freeNode.remove(valIdx);
////                matchedValues.set(valIdx);
////            } else {
////                // 检查原匹配是否失效
////                int oldMatchingIndex = var2Val[varIdx];
////                if (oldMatchingIndex != -1) {
////                    // 如果oldMatchingValue无效
////                    if (!v.contains(idx2Val[oldMatchingIndex])) {
////                        val2Var[oldMatchingIndex] = -1;
////                        var2Val[varIdx] = -1;
////                        varsTmp.add(varIdx);
////                    } else {
////                        //freeNode.remove(oldMatchingIndex);
////                        matchedValues.set(oldMatchingIndex);
////                    }
////                } else {
////                    varsTmp.add(varIdx);
////                }
////
////            }
////        }
////    }
//
//    protected void repairMatching(int SCCStartIndex) throws ContradictionException {
//        // repair max matching.
//        partition.setIteratorIndexBySCCStartIndex(SCCStartIndex);
//        while (partition.hasNext()) {
//            int varIdx = partition.next();
//            updateBitDom(varIdx);
//            int valIdx = var2ValR[varIdx].get();
//            // 值失效
//            if (valIdx == -1 || !D[varIdx].get(valIdx)) {
//                var2ValR[varIdx].set(-1);
//                visitedValues.clear();
//                unVisitedVariables.set(0, arity);
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
//    protected void CheckAndRepairMatching() throws ContradictionException {
//        varsTmp.iterateValid();
//        while (varsTmp.hasNextValid()) {
//            int varIdx = varsTmp.next();
//            if (var2ValR[varIdx].get() == -1) {
//                visitedValues.clear();
////                visitedVariables.clear();
//                unVisitedVariables.set(0, arity);
//                MakeAugmentingPath(varIdx);
//            }
//            if (var2ValR[varIdx].get() == -1) {
//                // No augmenting path exists.
////                System.out.println("match fail");
////                for (int i = 0; i < vars.length; i++) {
////                    monitors[i].unfreeze();
////                }
////                    System.out.println("match fail");
////                Measurer.matchingTime += System.nanoTime() - startTime;
//                vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
//            }
//        }
//    }
//
//    protected boolean propagate_SCC_Match() throws ContradictionException {
//        boolean res = false;
//        IntVar x, y;
//        // 匹配值清空
//
////        prepareForMatching();
//        changedSCCStartIndex.clear();
//        System.out.println(partition);
//        triggeringVars.iterateValid();
//        while (triggeringVars.hasNextValid()) {
//            int xIdx = triggeringVars.next();
//            updateBitDom(xIdx);
////            int valIdx = var2Val[xIdx];
//            int valIdx = var2ValR[xIdx].get();
//
//            int sccStartIdx = partition.getSCCStartIndexByElement(xIdx);
//            x = vars[xIdx];
//
//            // valIdx失效
//            if (valIdx == -1 || !D[xIdx].get(valIdx)) {
//                repairMatching(sccStartIdx);
//            }
//
//            if (x.isInstantiated() && !partition.isSingletonByStartIndex(sccStartIdx)) {
//                valIdx = var2ValR[xIdx].get();
////                updateBitBel(valIdx);
//                updateBitBel(valIdx);
//                int xVal = idx2Val[valIdx];
//                if (changedSCCStartIndex.contains(sccStartIdx)) {
//                    changedSCCStartIndex.remove(sccStartIdx);
//                }
//
//                //parition s into s1 s2 , from now on s = s2
////                System.out.println("partition remove: " + xIdx + " " + (val2Idx.get(xVal) + addArity));
////                System.out.println(partition);
//                partition.remove(xIdx);
//                System.out.println(xIdx + " is isInstantiated to: " + xVal);
//                System.out.println(partition);
//
//                partition.setIteratorIndexBySCCStartIndex(sccStartIdx);
//                while (partition.hasNext()) {
//                    int yIdx = partition.next();
//                    updateBitDom(yIdx);
//                    if (D[yIdx].get(valIdx)) {
//                        System.out.println("remove: " + yIdx + ", " + xVal);
//                        y = vars[yIdx];
//                        res |= y.removeValue(xVal, aCause);
//                        removeValue(yIdx, valIdx);
//                        deletedValues[yIdx].add(valIdx);
//                    }
//                }
//
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
////        CheckAndRepairMatching();
//        return res;
//    }
//
////    protected void prepareForMatching() {
////        //freeNode.fill();
//////        matchedValues.clear();
//////        varsTmp.clear();
////        // 增量检查
////        // matching 有效性检查
////        triggeringVars.iterateValid();
////        while (triggeringVars.hasNextValid()) {
//////        for (int varIdx = 0; varIdx < arity; varIdx++) {
////            int varIdx = triggeringVars.next();
////            updateBitDom(varIdx);
//////            IntVar v = vars[varIdx];
////            // !! 这里可以修改一下 已赋值 就不参与修改了
////            if (D[varIdx].size() == 1) {
////                // 取出变量的唯一值
////                int valIdx = D[varIdx].nextSetBit(0);
////                updateBitBel(valIdx);
////                int oldValIdx = var2ValR[varIdx].get();
////                int oldVarIdx = val2VarR[valIdx].get();
////
////                if (oldValIdx != -1 && oldValIdx != valIdx) {
////                    val2VarR[oldValIdx].set(-1);
////                    updateBitBel(oldValIdx);
////                }
////                if (oldVarIdx != -1 && oldVarIdx != varIdx) {
////                    var2ValR[oldVarIdx].set(-1);
////                    updateBitBel(oldVarIdx);
////                }
////
////                val2VarR[valIdx].set(varIdx);
////                var2ValR[varIdx].set(valIdx);
////                //freeNode.remove(valIdx);
////                matchedValues.set(valIdx);
////                if (oldValIdx != -1) {
////                    matchedValues.clear(oldValIdx);
////                }
////            } else {
////                // 检查原匹配是否失效
////                int oldMatchingIndex = var2ValR[varIdx].get();
////                if (oldMatchingIndex != -1) {
////                    // 如果oldMatchingValue无效
////                    if (!D[varIdx].get(oldMatchingIndex)) {
//////                    if (!D[varIdx].get(oldMatchingIndex)) {
////                        val2VarR[oldMatchingIndex].set(-1);
//////                        unMatchedValues.set(oldMatchingIndex);
////                        matchedValues.clear(oldMatchingIndex);
//////                        matchedValues.set(oldMatchingIndex);
////                        var2ValR[varIdx].set(-1);
////                    } else {
//////                        //freeNode.clear(oldMatchingIndex);
////                        //freeNode.remove(oldMatchingIndex);
////                        matchedValues.set(oldMatchingIndex);
//////                    System.out.println(oldMatchingIndex + " is free");
////                    }
////                }
////
////            }
////        }
////    }
//
//    protected boolean propagate_SCC_filter() throws ContradictionException {
////        distinguish();
////        initiateMatrix();
//        boolean filter = false;
////        unconnected = false;
////        unconnected = !gammaMask.isEmpty();
//        changedSCCStartIndex.iterateValid();
//        while (changedSCCStartIndex.hasNextValid()) {
//            int sccStartIndex = changedSCCStartIndex.next();
////            partition.getPartitionVars(sccStartIndex, varsTmp);
////            partition.setIteratorIndexBySCCStartIndex(sccStartIndex);
//            initiateMatrix(sccStartIndex);
//
//            filter |= filterDomains(sccStartIndex);
//
////            partition.getPartitionBitSetMaskAndVars(sccStartIndex, restriction, varsTmp, notGamma, valsTmp, notA, freeNodes, arity, numNodes);
////            resetData(varsTmp, valsTmp, restriction.get(arity));
////            if (freeNodes.validSize() != 0) {
////                propagateFreeNodes();
////            }
//////            System.out.println("valDFSNum: " + Arrays.toString(valDFSNum) + ", " + restriction + "," + partition);
////            findAllSCC(restriction, varsTmp);
////            filter |= filterDomains(varsTmp, valsTmp);
//        }
//        return filter;
//    }
//    //***********************************************************************************
//    // PRUNING
//    //***********************************************************************************
//
//
//    private void distinguish() {
//        notGamma.fill();
//        notA.fill();
//        gammaMask.clear();
//
//        freeNode.iterateValid();
//        while (freeNode.hasNextValid()) {
//            // 每个freeNode的值拿出来
////            System.out.println(i);
//            int valIdx = freeNode.next();
//            notA.remove(valIdx);
//            gammaMask.or(B[valIdx]);
//        }
//        gammaFrontier.set(gammaMask);
//
//        for (int varIdx = gammaFrontier.nextSetBit(0);
//             varIdx >= 0; varIdx = gammaFrontier.nextSetBit(0)) {
//            // !! 这里可以将Extended改成Frontier，只记录前沿，记录方法是三个BitSet比较，
//            // frontier 扩展，从valMask中去掉gammaMask已记录的变量
//            int valIdx = var2ValR[varIdx].get();
//            gammaFrontier.orAfterMinus(B[valIdx], gammaMask);
////            // 除去第i个变量
//            gammaFrontier.clear(varIdx);
//            // gamma 扩展
//            gammaMask.or(B[valIdx]);
//            notGamma.remove(varIdx);
//            notA.remove(valIdx);
//        }
//
//    }
//
//    private void initiateMatrix() {
//        // 重置两个矩阵
//        // 只重置notGamma的变量
//        notGamma.iterateValid();
//        while (notGamma.hasNextValid()) {
//            int varIdx = notGamma.next();
//            // 从变量id拿到匹配值再拿到该值所能到达的变量mask
//            if (!vars[varIdx].isInstantiated()) {
//                graphLinkedMatrix[varIdx].setAfterMinus(B[var2ValR[varIdx].get()], gammaMask);
//                graphLinkedMatrix[varIdx].clear(varIdx);
//                graphLinkedFrontier[varIdx].set(graphLinkedMatrix[varIdx]);
//            }
////                System.out.println("------graphLinkedMatrix[" + varIdx + "]------");
////                System.out.println(graphLinkedMatrix[varIdx]);
////                System.out.println(graphLinkedFrontier[varIdx]);
//        }
//    }
//
//    private void initiateMatrix(int sccStartIdx) {
//        // 重置两个矩阵
//        // 只重置notGamma的变量
//        partition.setIteratorIndexBySCCStartIndex(sccStartIdx);
//        while (partition.hasNext()) {
//
//            int varIdx = partition.next();
//            updateBitDom(varIdx);
//            // 从变量id拿到匹配值再拿到该值所能到达的变量mask
////            if (!vars[varIdx].isInstantiated()) {
//            int valIdx = var2ValR[varIdx].get();
//            updateBitBel(valIdx);
//            graphLinkedMatrix[varIdx].set(B[valIdx]);
////                graphLinkedMatrix[varIdx].setAfterMinus(B[valIdx], gammaMask);
//            graphLinkedMatrix[varIdx].clear(varIdx);
//            graphLinkedFrontier[varIdx].set(graphLinkedMatrix[varIdx]);
////            }
//            System.out.println("------graphLinkedMatrix[" + varIdx + "]------");
//            System.out.println(graphLinkedMatrix[varIdx]);
//            System.out.println(graphLinkedFrontier[varIdx]);
//        }
//
//    }
//
////    private boolean filter() throws ContradictionException {
////        distinguish();
////        initiateMatrix();
////        // 这里判断一下，如果notGamma为空则不用进行如下步骤
////        boolean filter = false;
////        for (int varIdx = 0; varIdx < arity; varIdx++) {
////            IntVar v = vars[varIdx];
////            if (!v.isInstantiated()) {
////                for (int valIdx = D[varIdx].nextSetBit(0); valIdx >= 0; valIdx = D[varIdx].nextSetBit(valIdx + 1)) {
////                    int k = idx2Val[valIdx];
//////                    System.out.println(valIdx);
////                    if (!notGamma.contains(varIdx) && notA.contains(valIdx)) {
////                        ++Measurer.numDelValuesP1;
////                        Measurer.enterP1();
//////                        D[varIdx].clear(valIdx);
////                        filter |= v.removeValue(k, aCause);
////                        removeValue(varIdx, valIdx);
////                        System.out.println("first delete: " + v.getName() + ", " + k);
////                    } else if (notGamma.contains(varIdx) && notA.contains(valIdx)) {
////                        if (!checkSCC(varIdx, valIdx)) {
////                            Measurer.enterP2();
////                            if (valIdx == var2ValR[varIdx].get()) {
////                                int valNum = v.getDomainSize();
////                                Measurer.numDelValuesP2 += valNum - 1;
////                                filter |= v.instantiateTo(k, aCause);
////                                instantiateTo(varIdx, valIdx);
//////                            System.out.println("instantiate  : " + v.getName() + ", " + k);
////                            } else {
////                                ++Measurer.numDelValuesP2;
////                                filter |= v.removeValue(k, aCause);
////                                removeValue(varIdx, valIdx);
////                                System.out.println("second delete: " + v.getName() + ", " + k);
////                            }
////                        }
////                    }
////                }
////            }
////        }
////        return filter;
////    }
//
////    private boolean filterDomains(int sccStartIndex, SparseSet filterVars) throws ContradictionException {
////        boolean filter = false;
////        filterVars.iterateValid();
////        while (filterVars.hasNextValid()) {
////            int varIdx = filterVars.next();
////            IntVar v = vars[varIdx];
////            if (!v.isInstantiated()) {
////                for (int valIdx = D[varIdx].nextSetBit(0); valIdx >= 0; valIdx = D[varIdx].nextSetBit(valIdx + 1)) {
////                    int k = idx2Val[valIdx];
////                    int varIdx2 = val2VarR[valIdx].get();
//////                    System.out.println(valIdx);
////                    if (!notGamma.contains(varIdx) && notA.contains(valIdx)) {
////                        ++Measurer.numDelValuesP1;
////                        Measurer.enterP1();
////                        filter |= v.removeValue(k, aCause);
////                        removeValue(varIdx, valIdx);
////                        //                System.out.println("first delete: " + v.getName() + ", " + k);
////                    } else if (notGamma.contains(varIdx) && notA.contains(valIdx)) {
////                        if (!checkSCC(varIdx, valIdx)) {
////                            Measurer.enterP2();
////                            if (valIdx == var2ValR[varIdx].get()) {
////                                int valNum = v.getDomainSize();
////                                Measurer.numDelValuesP2 += valNum - 1;
////                                filter |= v.instantiateTo(k, aCause);
////                                instantiateTo(varIdx, valIdx);
//////                            System.out.println("instantiate  : " + v.getName() + ", " + k);
////                            } else {
////                                ++Measurer.numDelValuesP2;
////                                filter |= v.removeValue(k, aCause);
////                                removeValue(varIdx, valIdx);
//////                            System.out.println("second delete: " + v.getName() + ", " + k);
////                            }
////                        }
//////                        else if (graphLinkedMatrix[varIdx2].get(varIdx)) {
//////                            sccMatrix[varIdx].set(varIdx2);
//////                            sccMatrix[varIdx2].set(valIdx);
//////                        }
////                    }
////                }
////            }
////        }
////
//////        // 装填SCC
//////        partition.setIteratorIndexBySCCStartIndex(sccStartIndex);
//////        filterVars.iterateValid();
//////        while (filterVars.hasNextValid()) {
//////            int x = filterVars.next();
//////            partition.add(x);
//////            for (int y = sccMatrix[x].nextSetBit(0); y != -1; y = sccMatrix[x].nextSetBit(y + 1)) {
//////                filterVars.remove(y);
//////                partition.add(y);
//////            }
//////            partition.setSplit();
//////
//////            if (filterVars.contains(x))
//////                filterVars.remove();
//////        }
////        return filter;
////    }
//
//    private boolean filterDomains(int sccStartIndex) throws ContradictionException {
//        boolean filter = false;
////        filterVars.iterateValid();
////        while (filterVars.hasNextValid()) {
////            int varIdx = filterVars.next();
//        partition.setIteratorIndexBySCCStartIndex(sccStartIndex);
//        while (partition.hasNext()) {
//            int varIdx = partition.nextAndSplitWhenMeetingUnknownAndMoved();
//            IntVar v = vars[varIdx];
//            if (!v.isInstantiated()) {
//                for (int valIdx = D[varIdx].nextSetBit(0); valIdx >= 0; valIdx = D[varIdx].nextSetBit(valIdx + 1)) {
//                    int k = idx2Val[valIdx];
//
//                    if (!checkSCC(varIdx, valIdx)) {
//                        Measurer.enterP2();
//                        int varIdx2 = val2VarR[valIdx].get();
//                        if (varIdx == varIdx2) {
//                            int valNum = v.getDomainSize();
//                            Measurer.numDelValuesP2 += valNum - 1;
//                            filter |= v.instantiateTo(k, aCause);
//                            instantiateTo(varIdx, valIdx);
//                            partition.removeCurrentToTail();
//                            System.out.println("instantiate  : " + v.getName() + ", " + k);
//                        } else {
//                            ++Measurer.numDelValuesP2;
//                            filter |= v.removeValue(k, aCause);
//                            removeValue(varIdx, valIdx);
//                            if (partition.canMove(varIdx2)) {
//                                // varIdx2未分裂，将varIdx2移入tmp分区中
//                                partition.addMoved(varIdx2);
//                            }
//                            System.out.println("second delete: " + v.getName() + ", " + k);
//                        }
//                    }
//////                    System.out.println(valIdx);
////                    if (!notGamma.contains(varIdx) && notA.contains(valIdx)) {
////                        ++Measurer.numDelValuesP1;
////                        Measurer.enterP1();
////                        filter |= v.removeValue(k, aCause);
////                        removeValue(varIdx, valIdx);
////                        //                System.out.println("first delete: " + v.getName() + ", " + k);
////                    } else if (notGamma.contains(varIdx) && notA.contains(valIdx)) {
////                        if (!checkSCC(varIdx, valIdx)) {
////                            Measurer.enterP2();
////                            if (valIdx == var2ValR[varIdx].get()) {
////                                int valNum = v.getDomainSize();
////                                Measurer.numDelValuesP2 += valNum - 1;
////                                filter |= v.instantiateTo(k, aCause);
////                                instantiateTo(varIdx, valIdx);
//////                            System.out.println("instantiate  : " + v.getName() + ", " + k);
////                            } else {
////                                ++Measurer.numDelValuesP2;
////                                filter |= v.removeValue(k, aCause);
////                                removeValue(varIdx, valIdx);
//////                            System.out.println("second delete: " + v.getName() + ", " + k);
////                            }
////                        }
//////                        else if (graphLinkedMatrix[varIdx2].get(varIdx)) {
//////                            sccMatrix[varIdx].set(varIdx2);
//////                            sccMatrix[varIdx2].set(valIdx);
//////                        }
////                    }
//                }
//            }
//        }
//        partition.disposeSCCIterator();
////        // 装填SCC
////        partition.setIteratorIndexBySCCStartIndex(sccStartIndex);
////        filterVars.iterateValid();
////        while (filterVars.hasNextValid()) {
////            int x = filterVars.next();
////            partition.add(x);
////            for (int y = sccMatrix[x].nextSetBit(0); y != -1; y = sccMatrix[x].nextSetBit(y + 1)) {
////                filterVars.remove(y);
////                partition.add(y);
////            }
////            partition.setSplit();
////
////            if (filterVars.contains(x))
////                filterVars.remove();
////        }
//        return filter;
//    }
//
//
//    private boolean checkSCC(int x, int a) {
////        System.out.println("check:" + varIdx + ", " + valIdx);
//        // 若没有 就需要BFS一下Frontier没有，就表示不用扩展了
//        // 注意一下return退出时frontier正确
//        // 确保x<y
//        int y = val2VarR[a].get();
////        int y;
////        if (x <= val2Var[a]) {
////            y = val2Var[a];
////        } else {
////            y = x;
////            x = val2Var[a];
////        }
//        if (graphLinkedMatrix[x].get(y)) {
//            return true;
//        }
//        for (int i = graphLinkedFrontier[x].nextSetBit(0);
//             i >= 0; i = graphLinkedFrontier[x].nextSetBit(0)) {
//            // frontier扩张，除掉变量i 因为变量i已被扩展。
//            graphLinkedFrontier[x].orAfterMinus(graphLinkedMatrix[i], graphLinkedMatrix[x]);
//            graphLinkedFrontier[x].clear(i);
//            graphLinkedMatrix[x].or(graphLinkedMatrix[i]);
//            if (graphLinkedMatrix[x].get(y)) {
//                return true;
//            }
//        }
//        return false;
//    }
//
//    void removeValue(int varIdx, int valIdx) {
//        D[varIdx].clear(valIdx);
//        RD[varIdx].clear(valIdx);
//        B[valIdx].clear(varIdx);
//        RB[valIdx].clear(varIdx);
//    }
//
//    void instantiateTo(int varIdx, int valIdx) {
//        D[varIdx].clear();
//        RD[varIdx].clear();
//        D[varIdx].set(valIdx);
//        RD[varIdx].set(valIdx);
//
//        B[valIdx].clear();
//        RB[valIdx].clear();
//        B[valIdx].set(varIdx);
//        RB[valIdx].set(varIdx);
//    }
//
//
//    // for lazy update, 最早在matching时，最晚在initiateMatrix时检测
//    void updateBitBel(int valIdx) {
//        // bit值未更新，此处更新
//        if (!updatedVals.contains(valIdx)) {
//            updatedVals.add(valIdx);
//            System.out.println("RB[" + valIdx + "]\t" + RB[valIdx]);
//            RB[valIdx].generateBitSet(B[valIdx]);
//            System.out.println("B[" + valIdx + "]\t" + B[valIdx]);
//        }
//    }
//
//    // for lazy update, 最早在matching时，最晚在initiateMatrix时检测
//    void updateBitDom(int varIdx) {
//        // bit值未更新，此处更新
//        if (!updatedVars.contains(varIdx)) {
//            updatedVars.add(varIdx);
//            System.out.println("RD[" + varIdx + "]\t" + RD[varIdx]);
//            RD[varIdx].generateBitSet(D[varIdx]);
//            System.out.println("D[" + varIdx + "]\t" + D[varIdx]);
//        }
//    }
//}
////
////
////    private void deltaUpdate() throws ContradictionException {
////        // 触发队列和更新队列
////        triggeringVars.clear();
////        triggeringVals.clear();
////        updatedVars.clear();
////        updatedVals.clear();
//////        lastBindVar = INDEX_OVERFLOW;
////
////        for (int varIdx = 0; varIdx < arity; varIdx++) {
////            monitors[varIdx].freeze();
////            int numDeltaSize = monitors[varIdx].sizeApproximation();
////            if (numDeltaSize != 0) {
////                // 变量发生改变
////                deletedValues[varIdx].clear();
////                triggeringVars.add(varIdx);
////                // 只动变量论域改变的变量，触发变量和删值队列都更新一下
//////                IntVar v = vars[varIdx];
////                monitors[varIdx].forEachRemVal(onValRem.set(varIdx));
//////                    D[varIdx].set(RD[varIdx]);
////                RD[varIdx].generateBitSet(D[varIdx]);
////                updatedVars.add(varIdx);
//////                if (v.isInstantiated()) {
//////                    // 变量刚刚被赋值
//////                    if (lastBindVar != INDEX_OVERFLOW)
//////                        System.out.println("error: multi bind");
//////                    lastBindVar = varIdx;
//////                    int valIdx = domIsRegular[varIdx] ? vars[varIdx].getValue() : val2Idx.get(vars[varIdx].getValue());
//////                    fillBitDBAfterInst(varIdx, valIdx);
//////                    updatedVars.add(varIdx);
////////                    updatedVals.add(valIdx);
//////                    triggeringVals.add(valIdx);
//////                } else {
//////                    // 否则更新
//////                    monitors[varIdx].forEachRemVal(onValRem.set(varIdx));
////////                    D[varIdx].set(RD[varIdx]);
//////                    RD[varIdx].generateBitSet(D[varIdx]);
//////                    updatedVars.add(varIdx);
//////                }
////            }
////            monitors[varIdx].unfreeze();
////        }
////    }
