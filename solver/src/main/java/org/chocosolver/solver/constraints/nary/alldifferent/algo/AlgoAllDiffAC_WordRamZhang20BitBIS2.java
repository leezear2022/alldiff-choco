package org.chocosolver.solver.constraints.nary.alldifferent.algo;

//import org.chocosolver.amtf.Measurer;

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.list.array.TIntArrayList;
import gnu.trove.map.hash.TIntIntHashMap;
import gnu.trove.stack.array.TLongArrayStack;
import org.chocosolver.memory.IEnvironment;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
import org.chocosolver.util.objects.*;
import org.chocosolver.util.procedure.UnaryIntProcedure;

import java.util.BitSet;

/**
 * Algorithm of Alldifferent with AC
 * <p>
 * Uses Zhang algorithm in the paper of IJCAI-18
 * "A Fast Algorithm for Generalized Arc Consistency of the Alldifferent Constraint"
 * <p>
 * We try to use the bit to speed up.
 * <p>
 * <p>
 *
 * @author Jean-Guillaume Fages, Zhe Li, Jia'nan Chen
 */
public class AlgoAllDiffAC_WordRamZhang20BitBIS2 {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************

    // 约束的个数
    static public int num = 0;
    private static int INT_SIZE = 32;
    // 约束的编号
    protected int id;
    protected static long numCall = -1;
    protected int arity;
    protected IntVar[] vars;
    protected ICause aCause;
    // 新增一点（视为变量）
    protected int addArity;
    // 自由值集合
    protected SparseSet freeNodes;
    // 以下是bit版本所需数据结构========================
    // numValue是二部图中取值编号的个数，numBit是二部图的最大边数
    protected int numValues;
    protected int numNodes;
    // 值到索引
    protected int[] idx2Val;

    //    // 与值相连的变量
//    protected INaiveBitSet[] B;
//    protected INaiveBitSet[] D;
    // 索引到值
    protected TIntIntHashMap val2Idx;
    // 已访问过的变量和值
    protected INaiveBitSet unVisitedVariables;
    protected INaiveBitSet unVisitedValues;
    protected INaiveBitSet matchedValues;
    // matching
    protected int[] val2Var;
    protected int[] var2Val;
    // 记录队列
    protected int[] visiting_;
    protected int[] variable_visited_from_;

    // for bit DFS Tarjan
    //栈
    protected int[] varStack;
    protected int[] valStack;
    protected INaiveBitSet varIsInStack;
    protected INaiveBitSet valIsInStack;
    protected int maxDFS = 0;
    protected int[] varDFSNum;
    protected int[] valDFSNum;
    protected int[] varLowLink;
    protected int[] valLowLink;
    protected boolean hasSCCSplit = false;
    protected boolean sinkIsUnvisited;
    protected int endBitIndex = 64;
    //for Gent
    protected RSetPartition partition;
    protected BitSet restriction;
    // for delta update
    protected IIntDeltaMonitor[] monitors;
    protected UnaryIntProcedure<Integer> onValRem;
    protected SparseSet triggeringVars;
    protected SparseSet changedSCCStartIndex;
    protected SparseSet varsTmp;
    protected SparseSet valsTmp;
    protected boolean initialPropagation = true;
    protected boolean unconnected = false;
    protected boolean isSkiped = false;
    //for bit
    protected INaiveBitSet[] B, D;
    protected INaiveBitSet needVisitValues;
    //    long startTime;
    //
    IEnvironment env;
    //boolean initialPropagate;
    int varStackIdx;
    int valStackIdx;
    int sinkDFSNum;
    int sinkLowLink;
    boolean sinkIsInStack;
    private TIntArrayList[] deletedValues;
    private TLongArrayStack DE;
    private BitIntervalSet cycles;
    private IntPair nodePair;
    // !! 记录gamma的前沿
    private INaiveBitSet gammaFrontier;
    // 记录gamma的bitset
    private INaiveBitSet gammaMask;

    // for propagate free nodes
    private SparseSet notGamma, notA;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_WordRamZhang20BitBIS2(IntVar[] variables, ICause cause, Model model) {
        id = num++;
        env = model.getEnvironment();
        this.vars = variables;
        aCause = cause;
        arity = vars.length;
        addArity = arity + 1;
        val2Idx = new TIntIntHashMap();
        IntVar v;
        // 统计所有变量论域中不同值的个数
        for (int i = 0; i < arity; ++i) {
            v = vars[i];
            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
                if (!val2Idx.containsKey(j)) {
                    val2Idx.put(j, val2Idx.size());
                }
            }
        }

        numValues = val2Idx.size();
        numNodes = addArity + numValues;

        idx2Val = new int[numValues];
        TIntIntIterator it = val2Idx.iterator();
        while (it.hasNext()) {
            it.advance();
            idx2Val[it.value()] = it.key();
        }

        // 记录访问过的变量
        visiting_ = new int[arity];
        unVisitedVariables = INaiveBitSet.makeBitSet(arity, true);
        // 变量的前驱变量，若前驱变量是-1，则表示无前驱变量，就是第一个变量
        variable_visited_from_ = new int[arity];
        unVisitedValues = INaiveBitSet.makeBitSet(numValues, true);
//        unMatchedValues = INaiveBitSet.makeBitSet(numValues, true);
        matchedValues = INaiveBitSet.makeBitSet(numValues, false);

        // for bit DFS
        varStack = new int[arity];
        valStack = new int[numValues];

        varIsInStack = INaiveBitSet.makeBitSet(arity, false);
        valIsInStack = INaiveBitSet.makeBitSet(numValues, false);

        varDFSNum = new int[arity];
        valDFSNum = new int[numValues];
        varLowLink = new int[arity];
        valLowLink = new int[numValues];

        var2Val = new int[arity];
        val2Var = new int[numValues];
        for (int i = 0; i < arity; ++i) {
            var2Val[i] = -1;
        }
        for (int i = 0; i < numValues; ++i) {
            val2Var[i] = -1;
        }

        freeNodes = new SparseSet(numValues);

        // for Gent algorithm
        partition = new RSetPartition(addArity + numValues, env);
        restriction = new BitSet(addArity + numValues);
        triggeringVars = new SparseSet(arity);
        changedSCCStartIndex = new SparseSet(numNodes);
        varsTmp = new SparseSet(arity);
        valsTmp = new SparseSet(numValues);

        monitors = new IIntDeltaMonitor[vars.length];
        for (int i = 0; i < vars.length; i++) {
            monitors[i] = vars[i].monitorDelta(cause);
        }
        onValRem = makeProcedure();

        // for bit
        B = new INaiveBitSet[numValues];
        for (int i = 0; i < numValues; ++i) {
            B[i] = INaiveBitSet.makeBitSet(arity, false);
        }

        D = new INaiveBitSet[arity];
        for (int i = 0; i < arity; ++i) {
            D[i] = INaiveBitSet.makeBitSet(numValues, false);
        }

        needVisitValues = INaiveBitSet.makeBitSet(numValues, true);
        gammaFrontier = INaiveBitSet.makeBitSet(arity, false);
        gammaMask = INaiveBitSet.makeBitSet(arity, false);
        // for zhang20
        DE = new TLongArrayStack();
        deletedValues = new TIntArrayList[arity];
        for (int i = 0; i < arity; i++) {
            deletedValues[i] = new TIntArrayList(numValues);
        }
        cycles = new BitIntervalSet(numNodes + 10);
        nodePair = new IntPair(-1, -1);

        // for propagate free nodes
        notA = new SparseSet(numValues);
        notGamma = new SparseSet(arity);
    }

    protected UnaryIntProcedure<Integer> makeProcedure() {
        return new UnaryIntProcedure<Integer>() {
            int var;
            // boolean isNotTrigger;
            IntVar v;

            @Override
            public UnaryIntProcedure set(Integer o) {
                var = o;
                v = vars[var];
                return this;
            }

            @Override
            public void execute(int i) {
                if (!triggeringVars.contains(var)) {
                    triggeringVars.add(var);
                    deletedValues[var].clear();
                }
                deletedValues[var].add(val2Idx.get(i));
            }
        };
    }

//    protected void fillD() {
////        IntVar v;
//        // 填充B和D
//        for (int i = 0; i < arity; ++i) {
//            D[i].clear();
//            IntVar v = vars[i];
//            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
//                int valIdx = val2Idx.get(j);
//                D[i].set(valIdx);
//            }
//        }
//    }

    protected void fillBandD() {
        for (int i = 0; i < numValues; ++i) {
            B[i].clear();
        }

        // 填充B和D
        for (int i = 0; i < arity; ++i) {
            D[i].clear();
            IntVar v = vars[i];
            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
                int valIdx = val2Idx.get(j);
                D[i].set(valIdx);
                B[valIdx].set(i);
            }
        }
    }

    void printDoms() {
        for (var v : vars) {
//            System.out.print(v.getId() + "\t\t: ");
//            for (int k = v.getLB(), ub = v.getUB(); k <= ub; k = v.nextValue(k)) {
//                System.out.print(k + " ");
//            }
//            System.out.println();
            System.out.println(v.getDomainSize());
        }
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    public boolean propagate() throws ContradictionException {
        isSkiped = false;
        boolean filter = false;
        Measurer.enterProp();
        long startTime;
        fillBandD();
        numCall++;

//        if (numCall == 308) {
        System.out.println("----------------" + id + " propagate: " + (numCall) + "----------------");
        printDoms();
//        }

        if (initialPropagation) {
            // initial
            restriction.set(0, numNodes);
            triggeringVars.fill();
            varsTmp.fill();
            valsTmp.fill();
            notA.fill();
            notGamma.fill();
            // matching
            startTime = System.nanoTime();
            findMaximumMatching();
            Measurer.matchingTime += System.nanoTime() - startTime;
//            System.out.println(matchedValues);
            // filtering
            startTime = System.nanoTime();
            resetData(varsTmp, valsTmp, true);
            if (freeNodes.validSize() != 0) {
                propagateFreeNodes();
            }
            findAllSCC(restriction, varsTmp);
            filter = filterDomains(varsTmp, valsTmp);
            Measurer.filterTime += System.nanoTime() - startTime;
            initialPropagation = false;
        } else {
            // initial
            triggeringVars.clear();
            for (int i = 0; i < arity; ++i) {
                monitors[i].freeze();
                monitors[i].forEachRemVal(onValRem.set(i));
                monitors[i].unfreeze();
            }
//            System.out.println("triggeringVars:" + triggeringVars);
//            System.out.println(partition);
//            System.out.println(Arrays.toString(var2Val));
//            System.out.println(Arrays.toString(val2Var));

            //matching
            startTime = System.nanoTime();
            filter |= propagate_SCC_Match();
            Measurer.matchingTime += System.nanoTime() - startTime;
//            System.out.println(matchedValues);
//            System.out.println(Arrays.toString(var2Val));
            //filtering
            startTime = System.nanoTime();
            filter |= propagate_SCC_filter();
//            System.out.println(partition);
            Measurer.filterTime += System.nanoTime() - startTime;
        }

        if (isSkiped) {
            Measurer.enterSkip();
        }
//        if (numCall == 308) {
        System.out.println("+++");
        printDoms();
//        }

        return filter;
    }

    protected boolean propagate_SCC_Match() throws ContradictionException {
        boolean res = false;
        IntVar x, y;
//        System.out.println("="+matchedValues);
        prepareForMatching();
//        System.out.println("="+matchedValues);
        changedSCCStartIndex.clear();
        triggeringVars.iterateValid();
        while (triggeringVars.hasNextValid()) {
            int xIdx = triggeringVars.next();
            int valIdx = var2Val[xIdx];
            int sccStartIdx = partition.getSCCStartIndexByElement(xIdx);
            x = vars[xIdx];

            if (valIdx == -1) {
                repairMatching(sccStartIdx);
            }

            if (x.isInstantiated() && partition.partitionSize(sccStartIdx) > 2) {
                valIdx = var2Val[xIdx];
                int xVal = idx2Val[valIdx];
                if (changedSCCStartIndex.contains(sccStartIdx)) {
                    changedSCCStartIndex.remove(sccStartIdx);
                }

                //parition s into s1 s2 , from now on s = s2
//                System.out.println("partition remove: " + xIdx + " " + (val2Idx.get(xVal) + addArity));
//                System.out.println("-" + partition);
                partition.remove(xIdx);
                partition.remove(valIdx + addArity);
//                System.out.println("-" + partition);
//                System.out.println(xIdx + " is isInstantiated to: " + xVal);
//                System.out.println(partition);
                partition.setIteratorIndexBySCCStartIndex(sccStartIdx);
                do {
                    int yIdx = partition.getValid();
                    if (yIdx < arity) {
                        y = vars[yIdx];
                        if (y.contains(xVal)) {
//                            System.out.println("remove: " + yIdx + ", " + xVal);
                            res |= y.removeValue(xVal, aCause);
                            D[yIdx].clear(valIdx);
                            B[valIdx].clear(yIdx);
                        }
                    }
                } while (partition.goToNextValid());

                if (partition.partitionSize(sccStartIdx) > 2) {
                    changedSCCStartIndex.add(sccStartIdx);
                }

            } else {
                if (partition.partitionSize(sccStartIdx) > 2) {
                    changedSCCStartIndex.add(sccStartIdx);
                }
            }
        }
        finalCheckAndRepairMatching();
        return res;
    }

    protected boolean propagate_SCC_filter() throws ContradictionException {
        boolean filter = false;
        maxDFS = 0;
//        System.out.println(Arrays.toString(var2Val));
//        System.out.println(Arrays.toString(val2Var));
//        unconnected = false;
        unconnected = !gammaMask.isEmpty();
        cycles.clear();
        changedSCCStartIndex.iterateValid();
        while (changedSCCStartIndex.hasNextValid()) {
            int sccStartIndex = changedSCCStartIndex.next();
//            System.out.println(partition);
            partition.getPartitionBitSetMaskAndVars(sccStartIndex, restriction, varsTmp, notGamma, valsTmp, notA, freeNodes, arity, numNodes);
            resetData(varsTmp, valsTmp, restriction.get(arity));

            if (freeNodes.validSize() != 0) {
                propagateFreeNodes();
            }

//            if (numCall == 308)
//                System.out.println("DE:" + DE);
//                System.out.println(partition);
//            System.out.println("free = " + freeNodes);
//            System.out.println(restriction);
//            System.out.println("valDFSNum: " + Arrays.toString(valDFSNum) + ", " + restriction + "," + partition);
//            System.out.println("DE: "+DE.size());
            findAllSCC(restriction, varsTmp);
            filter |= filterDomains(varsTmp, valsTmp);
        }
        return filter;
    }

    protected void prepareForMatching() {
        //freeNode.fill();
        matchedValues.clear();
        varsTmp.clear();
        // 增量检查
        // matching 有效性检查
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            IntVar v = vars[varIdx];
            // !! 这里可以修改一下 已赋值 就不参与修改了
            if (v.getDomainSize() == 1) {
                // 取出变量的唯一值
                int valIdx = val2Idx.get(v.getValue());

                int oldValIdx = var2Val[varIdx];
                int oldVarIdx = val2Var[valIdx];

                if (oldValIdx != -1 && oldValIdx != valIdx) {
                    val2Var[oldValIdx] = -1;
                }
                if (oldVarIdx != -1 && oldVarIdx != varIdx) {
                    var2Val[oldVarIdx] = -1;
                }

                val2Var[valIdx] = varIdx;
                var2Val[varIdx] = valIdx;
                //freeNode.remove(valIdx);
                matchedValues.set(valIdx);
            } else {
                // 检查原匹配是否失效
                int oldMatchingIndex = var2Val[varIdx];
                if (oldMatchingIndex != -1) {
                    // 如果oldMatchingValue无效
                    if (!v.contains(idx2Val[oldMatchingIndex])) {
                        val2Var[oldMatchingIndex] = -1;
                        var2Val[varIdx] = -1;
                        varsTmp.add(varIdx);
                    } else {
                        //freeNode.remove(oldMatchingIndex);
                        matchedValues.set(oldMatchingIndex);
                    }
                } else {
                    varsTmp.add(varIdx);
                }

            }
        }
    }

    protected void repairMatching(int SCCStartIndex) throws ContradictionException {
        // repair max matching.
//        System.out.println("repair matching: sccStartIndex: " + SCCStartIndex);
        partition.setIteratorIndexBySCCStartIndex(SCCStartIndex);
        do {
            int varIdx = partition.getValid();
//            if (id == 7) {
//                System.out.print(varIdx + " ");
//            }
            if (varIdx < arity) {
//                if (var2Val[varIdx] == -1) {
                if (var2Val[varIdx] == -1) {
                    unVisitedValues.set();
//                visitedVariables.clear();
                    unVisitedVariables.set();
                    MakeAugmentingPath(varIdx);
                }

                if (var2Val[varIdx] == -1) {
//                    for (int i = 0; i < vars.length; i++) {
//                        monitors[i].unfreeze();
//                    }
//                    System.out.println("match fail");
//                    Measurer.matchingTime += System.nanoTime() - startTime;
                    vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
                } else {
                    varsTmp.remove(varIdx);
                }
            }
        } while (partition.goToNextValid());
    }

    protected void finalCheckAndRepairMatching() throws ContradictionException {
        varsTmp.iterateValid();
        while (varsTmp.hasNextValid()) {
            int varIdx = varsTmp.next();
            if (var2Val[varIdx] == -1) {
                unVisitedValues.set();
//                visitedVariables.clear();
                unVisitedVariables.set();
                MakeAugmentingPath(varIdx);
            }
            if (var2Val[varIdx] == -1) {
                // No augmenting path exists.
//                System.out.println("match fail");
//                for (int i = 0; i < vars.length; i++) {
//                    monitors[i].unfreeze();
//                }
//                    System.out.println("match fail");
//                Measurer.matchingTime += System.nanoTime() - startTime;
                vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
            }
        }
    }

    //***********************************************************************************
    // Initialization
    //***********************************************************************************

    protected void MakeAugmentingPath(int start) {
//        System.out.println("MakeAugmentingPath: " + start);
        int num_to_visit = 0;
        int num_visited = 0;
        // visit 里存的是变量
        visiting_[num_to_visit++] = start;
        unVisitedVariables.clear(start);
        variable_visited_from_[start] = -1;

        while (num_visited < num_to_visit) {
            // Dequeue node to visit.
            int node = visiting_[num_visited++];
            IntVar v = vars[node];

            for (int value = v.getLB(), ub = v.getUB(); value <= ub; value = v.nextValue(value)) {
                int valIdx = val2Idx.get(value);
                if (!unVisitedValues.get(valIdx)) continue;
                unVisitedValues.clear(valIdx);
                if (!matchedValues.get(valIdx)) {
                    int path_node = node;
                    int path_value = valIdx;
                    while (path_node != -1) {
                        // 旧变量拿到旧匹配值
                        int old_value = var2Val[path_node];
                        // 旧变量拿到新匹配值
                        var2Val[path_node] = path_value;
                        val2Var[path_value] = path_node;

                        // 回溯到上一个变量
                        path_node = variable_visited_from_[path_node];
                        // 由于这个变量传递下去是连贯的，可以检查连通生，做为下一个阶段的记录
                        path_value = old_value;
                    }

//                    //freeNode.clear(valIdx);
                    //freeNode.remove(valIdx);
                    matchedValues.set(valIdx);
//                    System.out.println(valIdx + " is not free");
                    return;
                } else {
                    // Enqueue node matched to valIdx.
                    // 若没有该值已经有匹配，但变量没有匹配

                    // 先拿到这个值的匹配变量
                    int next_node = val2Var[valIdx];
//                    variable_visited_.set(next_node);
                    unVisitedVariables.clear(next_node);
                    // 把这个变量加入队列中
                    visiting_[num_to_visit++] = next_node;
                    variable_visited_from_[next_node] = node;
//                    //freeNode.clear(valIdx);
                    //freeNode.remove(valIdx);
                    matchedValues.set(valIdx);
                }
            }
        }
    }

    protected void findMaximumMatching() throws ContradictionException {
        //freeNode.fill();
        matchedValues.clear();

        // 增量检查
        // matching 有效性检查
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            IntVar v = vars[varIdx];
            // !! 这里可以修改一下 已赋值 就不参与修改了
//            if (v.getDomainSize() == 1) {
//                // 取出变量的唯一值
//                int valIdx = val2Idx.get(v.getValue());
//                B[valIdx].set(varIdx);
//                System.out.println(v.getName() + " : " + varIdx + " is singleton = " + v.getValue() + " : " + valIdx);
            if (v.getDomainSize() == 1) {
                // 取出变量的唯一值
                int valIdx = val2Idx.get(v.getValue());
//                System.out.println(v.getName() + " : " + varIdx + " is singleton = " + v.getValue() + " : " + valIdx);

                int oldValIdx = var2Val[varIdx];
                int oldVarIdx = val2Var[valIdx];

                if (oldValIdx != -1 && oldValIdx != valIdx) {
                    val2Var[oldValIdx] = -1;
//                    unMatchedValues.set(oldValIdx);
//                    matchedValues.clear(oldValIdx);
                }
                if (oldVarIdx != -1 && oldVarIdx != varIdx) {
                    var2Val[oldVarIdx] = -1;
                }

                val2Var[valIdx] = varIdx;
//                unMatchedValues.clear(valIdx);
                var2Val[varIdx] = valIdx;
                //freeNode.remove(valIdx);
                matchedValues.set(valIdx);
            } else {
                // 检查原匹配是否失效
                int oldMatchingIndex = var2Val[varIdx];
                if (oldMatchingIndex != -1) {
                    // 如果oldMatchingValue无效
                    if (!v.contains(idx2Val[oldMatchingIndex])) {
//                    if (!D[varIdx].get(oldMatchingIndex)) {
                        val2Var[oldMatchingIndex] = -1;
//                        unMatchedValues.set(oldMatchingIndex);
//                        matchedValues.clear(oldMatchingIndex);
                        var2Val[varIdx] = -1;
                    } else {
//                        //freeNode.clear(oldMatchingIndex);
                        //freeNode.remove(oldMatchingIndex);
                        matchedValues.set(oldMatchingIndex);
//                    System.out.println(oldMatchingIndex + " is free");
                    }
                }

            }
        }

        // Compute max matching.
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            if (var2Val[varIdx] == -1) {
//                value_visited_.clear();
                unVisitedValues.set();
//                visitedVariables.clear();
                unVisitedVariables.set();
                MakeAugmentingPath(varIdx);
            }
            if (var2Val[varIdx] == -1) {
                // No augmenting path exists.
//                Measurer.matchingTime += System.nanoTime() - startTime;
                vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
            }
        }

//        System.out.println(Arrays.toString(var2Val));
//        System.out.println(Arrays.toString(val2Var));
    }
    //***********************************************************************************
    // PRUNING
    //***********************************************************************************

    protected boolean filterDomains(SparseSet filterVars, SparseSet filterVals) throws ContradictionException {
//        if (numCall == 308)
//            System.out.println(partition);
//        if (numCall == 308)
//            System.out.println("filter: " + filterVars);
        boolean filter = false;
        filterVars.iterateValid();
        while (filterVars.hasNextValid()) {
            int varIdx = filterVars.next();
            IntVar v = vars[varIdx];
            if (!v.isInstantiated()) {
//                filterVals.iterateValid();
//                while (filterVals.hasNextValid()) {
//                    int valIdx = filterVals.next();
                for (int valIdx = D[varIdx].firstSetBit(); valIdx != D[varIdx].end(); valIdx = D[varIdx].nextSetBit(valIdx + 1)) {
//                int valIdx = filterVals.next();
                    int k = idx2Val[valIdx];
//                int ub = v.getUB();
//                for (int k = v.getLB(); k <= ub; k = v.nextValue(k)) {
//                    int valIdx = val2Idx.get(k);
//                    System.out.println(varIdx + ", " + valIdx + ", " + notGamma.contains(varIdx) + ", " + notA.contains(valIdx));
//                    if (!notGamma.contains(varIdx) && notA.contains(valIdx)) {
                    if (gammaMask.get(varIdx) && notA.contains(valIdx)) {
                        ++Measurer.numDelValuesP1;
                        Measurer.enterP1();
                        filter |= v.removeValue(k, aCause);
//                        if (numCall == 308)
//                            System.out.println("first delete: " + varIdx + ", " + k);
//                    } else if (notGamma.contains(varIdx) && notA.contains(valIdx)) {
                    } else if (!gammaMask.get(varIdx) && notA.contains(valIdx)) {
                        if (!partition.inSameSCC(varIdx, valIdx + addArity)) {
                            Measurer.enterP2();
                            if (valIdx == var2Val[varIdx]) {
                                int valNum = v.getDomainSize();
                                Measurer.numDelValuesP2 += valNum - 1;
                                filter |= v.instantiateTo(k, aCause);
//                                if (numCall == 308)
//                                    System.out.println("instantiate: " + varIdx + ", " + k);
                            } else {
                                ++Measurer.numDelValuesP2;
                                filter |= v.removeValue(k, aCause);
//                                if (numCall == 308)
//                                    System.out.println("second delete: " + varIdx + ", " + k);
//                            D[varIdx].clear(valIdx);
                            }
                        }
                    }
                }
            }
        }
        return filter;
    }

//    protected boolean filterDomains(SparseSet filterVars, SparseSet filterVals) throws ContradictionException {
//        boolean filter = false;
//        filterVars.iterateValid();
//        while (filterVars.hasNextValid()) {
//            int varIdx = filterVars.next();
//            IntVar v = vars[varIdx];
//            if (!v.isInstantiated()) {
//                filterVals.iterateValid();
//                while (filterVals.hasNextValid()) {
//                    int valIdx = filterVals.next();
//                    int k = idx2Val[valIdx];
////                int ub = v.getUB();
////                for (int k = v.getLB(); k <= ub; k = v.nextValue(k)) {
////                    int valIdx = val2Idx.get(k);
////                    System.out.println(varIdx+", "+valIdx);
//                    if (!partition.inSameSCC(varIdx, valIdx + addArity)) {
//                        Measurer.enterP2();
//                        if (valIdx == var2Val[varIdx]) {
//                            int valNum = v.getDomainSize();
//                            Measurer.numDelValuesP2 += valNum - 1;
//                            filter |= v.instantiateTo(k, aCause);
////                            System.out.println("instantiate: " + varIdx + ", " + k);
//                        } else {
//                            ++Measurer.numDelValuesP2;
//                            filter |= v.removeValue(k, aCause);
////                            D[varIdx].clear(valIdx);
////                            System.out.println("second delete: " + varIdx + ", " + k);
//                        }
//                    }
//                }
//            }
//        }
//        return filter;
//    }


    protected void resetData(SparseSet resetVars, SparseSet resetVals, boolean containsSink) {
//        maxDFS = 0;
//        cycles.clear();
        DE.clear();
        hasSCCSplit = false;
        gammaMask.clear();

        resetVals.iterateValid();
        while (resetVals.hasNextValid()) {
            int i = resetVals.next();
//            System.out.println("resetVal: " + i);
            valLowLink[i] = Integer.MAX_VALUE;
            valDFSNum[i] = Integer.MAX_VALUE;
        }

        resetVars.iterateValid();
        while (resetVars.hasNextValid()) {
            int i = resetVars.next();
//            System.out.println("resetVar: " + i);
            varLowLink[i] = Integer.MAX_VALUE;
            varDFSNum[i] = Integer.MAX_VALUE;
            // freeNodes设置成partition的全部值
            // 匹配值 都不可能是freeNodes集合的 把它们从freeNodes中删除
//            System.out.println("resetVar: " + i + "f remove: " + var2Val[i]);
            freeNodes.remove(var2Val[i]);
            if (triggeringVars.contains(i)) {
                var iter = deletedValues[i].iterator();
                while (iter.hasNext()) {
                    int valIdx = iter.next();
                    if (resetVals.contains(valIdx))
                        DE.push(getIntTuple2Long(i, valIdx));
                }
            }
        }

        if (containsSink) {
            sinkDFSNum = Integer.MAX_VALUE;
            sinkLowLink = Integer.MAX_VALUE;
            sinkIsInStack = false;
            sinkIsUnvisited = true;
        }

        unVisitedVariables.set();
        unVisitedValues.set();
    }

    // for propagate free node
    private void propagateFreeNodes() {
//        notGamma.clear();
//        notA.fill();
//         restriction记录寻找SCC的过程中未访问的变量
//        restriction.clear();
//        restriction.flip(0, arity);
//        notA.clear();
//        gammaMask.clear();

        int valIdx, varIdx;
        freeNodes.iterateValid();
        while (freeNodes.hasNextValid()) {
            valIdx = freeNodes.next();
            notA.remove(valIdx);
//            notGamma.remove (varIdx);
            gammaMask.or(B[valIdx]);
        }
//        gammaMask.and(restriction);
        gammaFrontier.set(gammaMask);
        for (varIdx = gammaFrontier.nextSetBit(0);
             varIdx != gammaFrontier.end();
             varIdx = gammaFrontier.nextSetBit(0)) {
            // !! 这里可以将Extended改成Frontier，只记录前沿，记录方法是三个BitSet比较，
            // frontier 扩展，从valMask中去掉gammaMask已记录的变量
            valIdx = var2Val[varIdx];
            gammaFrontier.orAfterMinus(B[valIdx], gammaMask);
            // 除去第i个变量
            gammaFrontier.clear(varIdx);
            // gamma 扩展
            gammaMask.or(B[valIdx]);
            notGamma.remove(varIdx);
            notA.remove(valIdx);
            restriction.clear(varIdx);
            restriction.clear(valIdx);
        }
//            notA.remove(valIdx);
        // 首先把与自由值相连的变量入队列
//            valUnmatchedVar[valIdx].iterateValid();
//            while (valUnmatchedVar[valIdx].hasNextValid()) {
//                varIdx = valUnmatchedVar[valIdx].next();
//                if (notGamma.contains(varIdx)) {
//                    fifo[indexLast++] = varIdx;
//                    notGamma.remove(varIdx);
//                    restriction.clear(varIdx);
//                }
//            }
        // 然后，对队列中每个变量的匹配值，把与该值相连的非匹配变量入队
//            while (indexFirst != indexLast) {
//                varIdx = fifo[indexFirst++];
//                valIdx = var2Val[varIdx];
//                notA.remove(valIdx);
//                valUnmatchedVar[valIdx].iterateValid();
//                while (valUnmatchedVar[valIdx].hasNextValid()) {
//                    varIdx = valUnmatchedVar[valIdx].next();
//                    if (notGamma.contains(varIdx)) {
//                        fifo[indexLast++] = varIdx;
//                        notGamma.remove(varIdx);
//                        restriction.clear(varIdx);
//                    }
//                }
//            }
    }


    boolean findAllSCC(BitSet restri, SparseSet resVars) {
        clearVarStack();
        clearValStack();

        findSingletons(restri, resVars);
//        if (numCall == 308)
//            System.out.println("restriction: " + restri);
//        System.out.println("partition: " + partition);
        for (int varIdx = restri.nextSetBit(0); varIdx >= 0 && varIdx < arity; varIdx = restriction.nextSetBit(varIdx + 1)) {
//            if (unVisitedVariables.get(varIdx)) {
//                System.out.println(varIdx);
//            if (numCall == 308)
//                System.out.printf("out: %d\n", varIdx);
            strongConnectVar(varIdx);
//            }
        }
        return false;
    }

    protected void findSingletons(BitSet restri, SparseSet resVars) {
//        singleton.clear();
        resVars.iterateValid();
//        for (int i = 0; i < arity; i++) {
        while (resVars.hasNextValid()) {
            int i = resVars.next();
            // 变量只有一个值，即只有匹配值
            // 若匹配边由变量指向值，若D[x]=1则表示变量x只有一个出边即匹配边，没有入边，即满足singleton条件
            IntVar v = vars[i];
            if (v.getDomainSize() == 1 && !partition.isSingleton(i)) {
//                varSCC[i] = nbSCC;
//                singleton.set(i);
                int totalIdx = valIndex2TotalIndex(var2Val[i]);
                restri.clear(i);
                restri.clear(totalIdx);
                partition.remove(i);
                partition.remove(totalIdx);
//                nbSCC++;
            }
        }
    }
//
//    protected void strongConnectVar(int curNode) {
////        System.out.println("scvr: " + curNode + ", " + maxDFS);
//        pushVarStack(curNode);
//        varDFSNum[curNode] = maxDFS;
//        varLowLink[curNode] = maxDFS;
//        maxDFS++;
//        unVisitedVariables.clear(curNode);
//
//        int matchedVal = var2Val[curNode];
//        IntVar v = vars[curNode];
//        for (int a = v.getLB(), ub = v.getUB(); a <= ub; a = v.nextValue(a)) {
//            int newNode = val2Idx.get(a);
//            if (newNode == matchedVal) continue;
////            System.out.println("scVartoVal: " + curNode + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
////            System.out.println(curNode + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
//            if (!unVisitedValues.get(newNode)) {
//                if (valIsInStack.get(newNode)) {
//                    varLowLink[curNode] = Math.min(varLowLink[curNode], valDFSNum[newNode]);
//                    if (!initialPropagation &&  !unconnected &&DE.size() != 0) DETest(valLowLink[newNode], maxDFS - 1);
//                }
//            } else {
//                strongConnectVal(newNode);
//                varLowLink[curNode] = Math.min(varLowLink[curNode], valLowLink[newNode]);
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
//
//        if ( !initialPropagation && !unconnected && (DE.size() == 0)) {
////            System.out.println("xixi");
//            isSkiped = true;
//            return;
//        }
//    }
//
//    protected void strongConnectVal(int curNode) {
////        System.out.println("scvl: " + curNode + ", " + maxDFS);
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
//                    if (!initialPropagation &&  !unconnected &&DE.size() != 0) DETest(varLowLink[matchedVar], maxDFS - 1);
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
//                    if (!initialPropagation &&  !unconnected &&DE.size() != 0) DETest(sinkLowLink, maxDFS - 1);
//                }
//            } else {
//                strongConnectSink();
//                valLowLink[curNode] = Math.min(valLowLink[curNode], sinkLowLink);
//            }
//        }
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
//        if ( !initialPropagation && !unconnected && (DE.size() == 0)) {
////            System.out.println("xixi");
//            isSkiped = true;
//            return;
//        }
//    }
//
//    protected void strongConnectSink() {
////        System.out.println("scs: " + ", " + maxDFS);
//        sinkIsInStack = true;
//        sinkDFSNum = maxDFS;
//        sinkLowLink = maxDFS;
//        maxDFS++;
//        sinkIsUnvisited = false;
////        Iterator<Integer> iterator = graph.getSuccOf(curNode).iterator();
////        while (iterator.hasNext()) {
////            int newNode = iterator.next();
//////            System.out.println(curNode + ", " + newNode + ", " + unvisited.get(newNode));
////            if (!unvisited.get(newNode)) {
////                if (inStack.get(newNode)) {
////                    lowLink[curNode] = Math.min(lowLink[curNode], DFSNum[newNode]);
////                }
////            } else {
////                strongConnectR(newNode);
////                lowLink[curNode] = Math.min(lowLink[curNode], lowLink[newNode]);
////            }
////        }
//
//        for (int newNode = matchedValues.firstSetBit(); newNode != matchedValues.end(); newNode = matchedValues.nextSetBit(newNode + 1)) {
////            System.out.println("scSinktoVal: " + arity + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
////            System.out.println(arity + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
//            if (!unVisitedValues.get(newNode)) {
//                if (valIsInStack.get(newNode)) {
//                    sinkLowLink = Math.min(sinkLowLink, valDFSNum[newNode]);
//                    if (!initialPropagation &&  !unconnected &&DE.size() != 0) DETest(valLowLink[newNode], maxDFS - 1);
//                }
//            } else {
//                strongConnectVal(newNode);
//                sinkLowLink = Math.min(sinkLowLink, valLowLink[newNode]);
//            }
//        }
//
////        long values = 0;
////        int newNode = 0, iBase = 0;
////        int i = 0;
////        for (int iWord = matchedValues.firstSetBit(); iWord <= matchedValues.lastSetIndex(); ++iWord) {
////            values = matchedValues.getWord(iWord) & ~unVisitedValues.getWord(iWord) & valIsInStack.getWord(iWord);
////            iBase = iWord * 64;
////            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
////                newNode = iBase + i;
////                sinkLowLink = Math.min(sinkLowLink, valDFSNum[newNode]);
////            }
////
//////            values = matchedValues.getWord(iWord) & unVisitedValues.getWord(iWord);
//////            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
//////                newNode = iBase + i;
//////                strongConnectVal(newNode);
//////                sinkLowLink = Math.min(sinkLowLink, valLowLink[newNode]);
//////                values &= unVisitedValues.getWord(iWord);
//////            }
////
////            values = matchedValues.getWord(iWord) & unVisitedValues.getWord(iWord);
////            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
////                newNode = iBase + i;
////                strongConnectVal(newNode);
////                sinkLowLink = Math.min(sinkLowLink, valLowLink[newNode]);
////                values &= unVisitedValues.getWord(iWord);
////            }
////        }
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
//        if ( !initialPropagation && !unconnected && (DE.size() == 0)) {
////            System.out.println("xixi");
//            isSkiped = true;
//            return;
//        }
////        System.out.println("back");
//    }

    protected void strongConnectVar(int curNode) {
        pushVarStack(curNode);
        varDFSNum[curNode] = maxDFS;
        varLowLink[curNode] = maxDFS;
        maxDFS++;
        unVisitedVariables.clear(curNode);

//         p2
        long values = 0;
        int newNode = 0, iBase = 0;
        int matchedVal = var2Val[curNode];
        int i = 0;
        for (int iWord = D[curNode].firstSetIndex(); iWord <= D[curNode].lastSetIndex(); ++iWord) {
            values = D[curNode].getWord(iWord) & valIsInStack.getWord(iWord);
            iBase = iWord * 64;
//            System.out.println(D[curNode]);
//            System.out.println(curNode + ": " + Long.toBinaryString(D[curNode].getWord(iWord)) + ": " + Long.toBinaryString(valIsInStack.getWord(iWord)) + ": " + Long.toBinaryString(values));

            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
                newNode = iBase + i;
                if (newNode == matchedVal) continue;
                varLowLink[curNode] = Math.min(varLowLink[curNode], valDFSNum[newNode]);
                if (!initialPropagation && !unconnected && DE.size() != 0) DETest(valLowLink[newNode], maxDFS - 1);
            }

            values = D[curNode].getWord(iWord) & unVisitedValues.getWord(iWord);
            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
                newNode = iBase + i;
                strongConnectVal(newNode);
                varLowLink[curNode] = Math.min(varLowLink[curNode], valLowLink[newNode]);
                values &= unVisitedValues.getWord(iWord);
            }
        }

        if (varLowLink[curNode] == varDFSNum[curNode]) {
            if (varLowLink[curNode] > 0 || valIsInStack.size() + varIsInStack.size() > 0) {
                hasSCCSplit = true;
            }
            if (hasSCCSplit) {
                processSCC(varDFSNum[curNode]);
            }
        }
//        System.out.println("back");
        if (!initialPropagation && !unconnected && (DE.size() == 0)) {
//            System.out.println("xixi");
            isSkiped = true;
            return;
        }
    }

    protected void strongConnectVal(int curNode) {
        pushValStack(curNode);
        valDFSNum[curNode] = maxDFS;
        valLowLink[curNode] = maxDFS;
        maxDFS++;
        unVisitedValues.clear(curNode);
        int matchedVar = val2Var[curNode];
        if (matchedVar != -1) {
            //have matched variable
//            System.out.println("scValtoVar: " + (addArity + curNode) + ", " + matchedVar + ", " + unVisitedVariables.get(matchedVar));
//            System.out.println((addArity + curNode) + ", " + matchedVar + ", " + unVisitedVariables.get(matchedVar));
            if (!unVisitedVariables.get(matchedVar)) {
                if (varIsInStack.get(matchedVar)) {
                    valLowLink[curNode] = Math.min(valLowLink[curNode], varDFSNum[matchedVar]);
                    if (!initialPropagation && DE.size() != 0 && !unconnected)
                        DETest(varLowLink[matchedVar], maxDFS - 1);
                }
            } else {
                strongConnectVar(matchedVar);
                valLowLink[curNode] = Math.min(valLowLink[curNode], varLowLink[matchedVar]);
            }
        } else {
            //free node successor node is sink node
//            System.out.println("scValtoSink: " + (addArity + curNode) + ", " + arity + ", " + sinkIsUnvisited);
//            System.out.println((addArity + curNode) + ", " + arity + ", " + sinkIsUnvisited);
            if (!sinkIsUnvisited) {
                if (sinkIsInStack) {
                    valLowLink[curNode] = Math.min(valLowLink[curNode], sinkDFSNum);
                    if (!initialPropagation && !unconnected && DE.size() != 0) DETest(sinkLowLink, maxDFS - 1);
                }
            } else {
                strongConnectSink();
                valLowLink[curNode] = Math.min(valLowLink[curNode], sinkLowLink);
            }
        }
//        Iterator<Integer> iterator = graph.getSuccOf(curNode).iterator();
//        //B[]
//        while (iterator.hasNext()) {
//            int newNode = iterator.next();
////            System.out.println(curNode + ", " + newNode + ", " + unvisited.get(newNode));
//            if (!unVisitedVariables.get(newNode)) {
//                if (valIsInStack.get(newNode)) {
//                    valLowLink[curNode] = Math.min(valLowLink[curNode], varDFSNum[newNode]);
//                }
//            } else {
//                // 判断一下sink节点
//                strongConnectR(newNode);
//                lowLink[curNode] = Math.min(lowLink[curNode], lowLink[newNode]);
//            }
//        }

//        System.out.println(curNode + " has no nei " + lowLink[curNode] + ", " + DFSNum[curNode]);
        if (valLowLink[curNode] == valDFSNum[curNode]) {
            if (valLowLink[curNode] > 0 || valIsInStack.size() + varIsInStack.size() > 0) {
                hasSCCSplit = true;
            }
            if (hasSCCSplit) {
                processSCC(valDFSNum[curNode]);
            }
        }

        if (!initialPropagation && !unconnected && (DE.size() == 0)) {
//            System.out.println("xixi");
            isSkiped = true;
            return;
        }
//        System.out.println("back");
    }

    protected void strongConnectSink() {
        sinkIsInStack = true;
        sinkDFSNum = maxDFS;
        sinkLowLink = maxDFS;
        maxDFS++;
        sinkIsUnvisited = false;

        long values = 0;
        int newNode = 0, iBase = 0;
        int i = 0;
        for (int iWord = matchedValues.firstSetIndex(); iWord <= matchedValues.lastSetIndex(); ++iWord) {
            values = matchedValues.getWord(iWord) & ~unVisitedValues.getWord(iWord) & valIsInStack.getWord(iWord);
            iBase = iWord * 64;
            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
                newNode = iBase + i;
                sinkLowLink = Math.min(sinkLowLink, valDFSNum[newNode]);
                if (!initialPropagation && !unconnected && DE.size() != 0) DETest(valLowLink[newNode], maxDFS - 1);
            }

//            values = matchedValues.getWord(iWord) & unVisitedValues.getWord(iWord);
//            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
//                newNode = iBase + i;
//                strongConnectVal(newNode);
//                sinkLowLink = Math.min(sinkLowLink, valLowLink[newNode]);
//                values &= unVisitedValues.getWord(iWord);
//            }

            values = matchedValues.getWord(iWord) & unVisitedValues.getWord(iWord);
            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
                newNode = iBase + i;
                strongConnectVal(newNode);
                sinkLowLink = Math.min(sinkLowLink, valLowLink[newNode]);
                values &= unVisitedValues.getWord(iWord);
            }
        }

//        System.out.println(curNode + " has no nei " + lowLink[curNode] + ", " + DFSNum[curNode]);
        if (sinkLowLink == sinkDFSNum) {
            if (sinkLowLink > 0 || sinkIsInStack || valIsInStack.size() + varIsInStack.size() > 0) {
                hasSCCSplit = true;
            }
            if (hasSCCSplit) {
                processSCC(sinkDFSNum);
            }
        }

        if (!initialPropagation && !unconnected && (DE.size() == 0)) {
//            System.out.println("xixi");
            isSkiped = true;
            return;
        }
//        System.out.println("back");
    }

    protected void processSCC(int rootNum) {
//        for (int valIdx = valIsInStack.firstSetBit(); valIdx !=INaiveBitSet.INDEX_OVERFLOW; valIdx=valIsInStack.++) {
//
//        }
//        System.out.println("scc: " + rootNum);
        int stackNode = -1;
//        sccSize = 0;
//        int limit;
        if (varStackIdx > 0 && varDFSNum[varStack[varStackIdx - 1]] >= rootNum) {
            int x = getTopVarStack();
            partition.resetLimitByElement(x);
        } else if (valStackIdx > 0 && valDFSNum[valStack[valStackIdx - 1]] >= rootNum) {
            int x = getTopValStack();
            partition.resetLimitByElement(valIndex2TotalIndex(x));
        }
//        if (valStackIdx != 0) {
//            stackNode = valStack[valStackIdx - 1];
        while (valStackIdx > 0 && valDFSNum[valStack[valStackIdx - 1]] >= rootNum) {
            stackNode = popValStack();
//            System.out.println("pop val: " + (addArity + stackNode) + ", " + stackNode + ", " + nbSCC + "," + valDFSNum[stackNode]);
            partition.add(valIndex2TotalIndex(stackNode));
            restriction.clear(valIndex2TotalIndex(stackNode));
//            valSCC[stackNode] = nbSCC;
//            sccSize++;
        }
//        }

//        if (varStackIdx != 0) {
//            stackNode = varStack[varStackIdx - 1];
        while (varStackIdx > 0 && varDFSNum[varStack[varStackIdx - 1]] >= rootNum) {
            stackNode = popVarStack();
//            System.out.println("pop var: " + stackNode + ", " + nbSCC + "," + varDFSNum[stackNode]);
//            varSCC[stackNode] = nbSCC;
            restriction.clear(stackNode);
            partition.add(stackNode);
//            sccSize++;
        }
//        }

        if (sinkIsInStack && sinkDFSNum >= rootNum) {
            partition.add(arity);
            restriction.clear(arity);
            sinkIsInStack = false;
        }

        partition.setSplit();
        unconnected = true;
//        System.out.println("partition: " + partition);
//        nbSCC++;
    }

    protected void pushVarStack(int v) {
        varStack[varStackIdx++] = v;
        varIsInStack.set(v);
    }

    protected void clearVarStack() {
        varIsInStack.clear();
        varStackIdx = 0;
    }

    protected int popVarStack() {
        int x = varStack[--varStackIdx];
        varIsInStack.clear(x);
        return x;
    }

    protected void pushValStack(int v) {
        valStack[valStackIdx++] = v;
        valIsInStack.set(v);
    }

    protected void clearValStack() {
        valIsInStack.clear();
        valStackIdx = 0;
    }

    protected int popValStack() {
        int x = valStack[--valStackIdx];
        valIsInStack.clear(x);
        return x;
    }

    public int nextSetBit(long words, int bitIndex) {
        return Long.numberOfTrailingZeros(words & -1L << bitIndex);
    }

    protected int getTopVarStack() {
        return varStack[varStackIdx - 1];
    }

    protected int getTopValStack() {
        return valStack[valStackIdx - 1];
    }

    int totalIndex2ValIndex(int totalIndex) {
        return totalIndex - addArity;
    }

    int valIndex2TotalIndex(int valIndex) {
        return valIndex + addArity;
    }

    private void DETest(int lowLinkNewNode, int dfs) {
//        System.out.println("DETest: " + lowLinkNewNode + ", " + dfs + " unconnected: " + unconnected + " DE Size: " + DE.size());
        cycles.add(lowLinkNewNode, dfs);
        while (!(DE.size() == 0) && inCycles(DE.peek())) {
            DE.pop();
        }
    }

//    private void addCycles(long e) {
//        for (int i = 0; i < cycles.size(); i++) {
//            long c = cycles.get(i);
//            if (overlap(c, e)) {
//                cycles.set(i, expand(c, e));
//                return;
//            }
//        }
//        cycles.add(e);
//    }

    private boolean inCycles(long f) {
//        IntTuple2 tt;
        getIntTuple2(nodePair, f);
//        System.out.println("inc:" + nodePair.a + "," + nodePair.b + "=" + varDFSNum[nodePair.a] + "," + valDFSNum[nodePair.b]);
        // 小的存入a大的存入b
        if (varDFSNum[nodePair.a] == Integer.MAX_VALUE || valDFSNum[nodePair.b] == Integer.MAX_VALUE) {
            return false;
        }

        int a, b;
        if (varDFSNum[nodePair.a] <= valDFSNum[nodePair.b]) {
            a = varDFSNum[nodePair.a];
            b = valDFSNum[nodePair.b];
        } else {
            a = valDFSNum[nodePair.b];
            b = varDFSNum[nodePair.a];
        }

        if (cycles.contains(a, b)) {
            return true;
        }

        return false;
    }

    public long getIntTuple2Long(int x, int a) {
        long c = x;
        return c << INT_SIZE | a;
    }

    public void getIntTuple2(IntPair vvp, long vvpIdx) {
        vvp.a = (int) (vvpIdx >> INT_SIZE);
        vvp.b = (int) vvpIdx;
    }

    private boolean cover(long e, int dfsa, int dfsb) {
        int a = (int) (e >> INT_SIZE);
        if (a == Integer.MAX_VALUE)
            return false;
        int b = (int) e;
        if (b == Integer.MAX_VALUE)
            return false;
//        int a = (int) (f >> INT_SIZE);
//        int b = (int) f;

        return (dfsa >= a && dfsa <= b) && (dfsb >= a && dfsb <= b);
    }

    private boolean overlap(long e, long f) {
        int a = (int) (e >> INT_SIZE);
//        if (a == Integer.MAX_VALUE)
//            return false;
        int b = (int) e;
//        if (b == Integer.MAX_VALUE)
//            return false;
        int x = (int) (f >> INT_SIZE);
//        if (x == Integer.MAX_VALUE)
//            return false;
        int y = (int) f;
//        if (y == Integer.MAX_VALUE)
//            return false;
//        System.out.println("overlap: " + x + "," + y + "," + a + "," + b);
        return (x >= a && x <= b) || (y >= a && y <= b);
    }

    private long expand(long e, long f) {
        int x = (int) (e >> INT_SIZE);
        int y = (int) e;
        int a = (int) (f >> INT_SIZE);
        int b = (int) f;
        return getIntTuple2Long(Math.min(x, a), Math.max(y, b));
    }
}