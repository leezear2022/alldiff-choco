package org.chocosolver.solver.constraints.nary.alldifferent.algo;

//import org.chocosolver.amtf.Measurer;

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.map.hash.TIntIntHashMap;
import org.chocosolver.memory.IEnvironment;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
import org.chocosolver.util.objects.INaiveBitSet;
import org.chocosolver.util.objects.Measurer;
import org.chocosolver.util.objects.RSetPartition;
import org.chocosolver.util.objects.SparseSet;
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
public class AlgoAllDiffAC_WordRamGentDebug extends AlgoAllDiffAC_Naive {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************
    // 约束的个数
    static public int num = 0;

    // 约束的编号
    private int id;
    private long numCall = -1;

    private int arity;
    private IntVar[] vars;
    private ICause aCause;

    // 新增一点（视为变量）
    private int addArity;

    // 自由值集合
    private SparseSet freeNode;

    // 以下是bit版本所需数据结构========================
    // numValue是二部图中取值编号的个数，numBit是二部图的最大边数
    private int numValues;

    private int numNodes;
    // 值到索引
    private int[] idx2Val;
    // 索引到值
    private TIntIntHashMap val2Idx;

//    // 与值相连的变量
//    private INaiveBitSet[] B;
//    private INaiveBitSet[] D;

    // 已访问过的变量和值
//    private INaiveBitSet visitedVariables;
    private INaiveBitSet unVisitedVariables;
    //    private INaiveBitSet value_visited_;
    private INaiveBitSet unVisitedValues;
    private INaiveBitSet needVisitValues;
    //    private INaiveBitSet unMatchedValues;
    private INaiveBitSet matchedValues;
//    private INaiveBitSet matchedMasks;

    //    private INaiveBitSet varSingletonMask;
//    private INaiveBitSet valSingletonMask;
//    private INaiveBitSet varTmpMask;
    // matching
    private int[] val2Var;
    private int[] var2Val;

    // 记录队列
    private int[] visiting_;
    private int[] variable_visited_from_;

    long startTime;
    //
    IEnvironment env;

    // for bit DFS Tarjan

    //栈
    private int[] varStack;
    private int[] valStack;
    private INaiveBitSet varIsInStack;
    private INaiveBitSet valIsInStack;
    int varStackIdx;
    int valStackIdx;

    // 标记SCC
//    private int nbSCC;
//    private int[] varSCC;
//    private int[] valSCC;

    private int maxDFS = 1;
    private int[] varDFSNum;
    private int[] valDFSNum;
    private int[] varLowLink;
    private int[] valLowLink;
    private boolean hasSCCSplit = false;
//    private int sccSize = 0;

    int sinkDFSNum;
    int sinkLowLink;
    boolean sinkIsInStack;

    //    private INaiveBitSet singleton;
    private boolean sinkIsUnvisited;

    private int endBitIndex = 64;


    //for Gent
    private RSetPartition partition;
    private BitSet restriction;
    // for delta update
    protected IIntDeltaMonitor[] monitors;
    private UnaryIntProcedure<Integer> onValRem;
    private SparseSet triggeringVars;
    //    private TIntHashSet changedSCCStartIndex;
    private SparseSet changedSCCStartIndex;
    private SparseSet varsTmp;
    private SparseSet valsTmp;
//    private BitSet filterVars;

    private boolean initialPropagation = true;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_WordRamGentDebug(IntVar[] variables, ICause cause, Model model) {
        super(variables, cause);
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
//        visitedVariables = INaiveBitSet.makeBitSet(arity, false);
        unVisitedVariables = INaiveBitSet.makeBitSet(arity, true);
        // 变量的前驱变量，若前驱变量是-1，则表示无前驱变量，就是第一个变量
        variable_visited_from_ = new int[arity];
//        value_visited_ = INaiveBitSet.makeBitSet(numValues, false);
        unVisitedValues = INaiveBitSet.makeBitSet(numValues, true);
        needVisitValues = INaiveBitSet.makeBitSet(numValues, true);
//        unMatchedValues = INaiveBitSet.makeBitSet(numValues, true);
        matchedValues = INaiveBitSet.makeBitSet(numValues, false);
//        matchedMasks = INaiveBitSet.makeBitSet(numValues, true);
//        varSingletonMask = INaiveBitSet.makeBitSet(arity, false);
//        valSingletonMask = INaiveBitSet.makeBitSet(numValues, false);
//        singleton = INaiveBitSet.makeBitSet(arity, false);
//        varTmpMask = INaiveBitSet.makeBitSet(arity, false);

        // for bit DFS
        varStack = new int[arity];
        valStack = new int[numValues];

        varIsInStack = INaiveBitSet.makeBitSet(arity, false);
        valIsInStack = INaiveBitSet.makeBitSet(numValues, false);

//        varSCC = new int[arity];
//        valSCC = new int[numValues];

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

        freeNode = new SparseSet(numValues);

        // for Gent algorithm
        partition = new RSetPartition(addArity + numValues, env);
        restriction = new BitSet(addArity + numValues);
        triggeringVars = new SparseSet(arity);
        changedSCCStartIndex = new SparseSet(numNodes);
        varsTmp = new SparseSet(arity);
        valsTmp = new SparseSet(numValues);
//        filterVars = new BitSet(arity);

        monitors = new IIntDeltaMonitor[vars.length];
        for (int i = 0; i < vars.length; i++) {
            monitors[i] = vars[i].monitorDelta(cause);
        }
        onValRem = makeProcedure();
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
                // isNotTrigger = true;
                return this;
            }

            @Override
            public void execute(int i) {
                if (!triggeringVars.contains(var)) {
                    triggeringVars.add(var);
                }

            }
        };
    }

    void printDoms() {
        for (var v : vars) {
            System.out.print(v.getId() + "\t\t: ");
            for (int k = v.getLB(), ub = v.getUB(); k <= ub; k = v.nextValue(k)) {
                System.out.print(k + " ");
            }
            System.out.println();
        }
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************


    public boolean propagate() throws ContradictionException {
        numCall++;
//        if (numCall<20) {
//        System.out.println("----------------" + id + " propagate: " + numCall + "----------------");
//            printDoms();
//        }

//        if (id == 2 && numCall == 14)


        boolean filter = false;
        Measurer.enterProp();
        long startTime;

        if (initialPropagation) {
            // initial
            restriction.set(0, numNodes);
            triggeringVars.fill();
            varsTmp.fill();
            initialPropagation = false;
            // matching
//            System.out.println("trig: " + triggeringVars);
            startTime = System.nanoTime();
//            prepareForMatching();
            findMaximumMatching();
            Measurer.matchingTime += System.nanoTime() - startTime;
//            System.out.println(Arrays.toString(var2Val));
            // filtering
            startTime = System.nanoTime();
            resetData(restriction);
            findAllSCC(restriction, varsTmp);
//            System.out.println(partition);
            filter = filterDomains(varsTmp);
            Measurer.filterTime += System.nanoTime() - startTime;
        } else {
//            DE.clear();
//            triggeringVars.clear();
            // initial
            triggeringVars.clear();
            for (int i = 0; i < arity; ++i) {
                monitors[i].freeze();
                monitors[i].forEachRemVal(onValRem.set(i));
                monitors[i].unfreeze();
            }
//            printDoms();
//            System.out.println("trig: " + triggeringVars);
//            SCCfinder.getAllSCCStartIndices(SCCStartIndex);
//            if (id == 2 && numCall == 14)
//                System.out.println("triggeringVars: " + triggeringVars);
//            if (id == 2 && numCall == 14)
//                System.out.println("before repair: " + Arrays.toString(var2Val));
//            if (id == 2 && numCall == 14)
//                System.out.println("before repair: " + partition);

            //matching
            startTime = System.nanoTime();
//            if (id == 30 && numCall == 68) {
//                System.out.println("triggeringVars: " + triggeringVars);
//                System.out.println("before repair: " + Arrays.toString(var2Val));
//                System.out.println("partition: " + partition);
//            }
//            }
//            if (id == 7) {
//                System.out.println("before repair: " + Arrays.toString(var2Val));
//                System.out.println(partition);
//            }
//            prepareForMatching();
//            if (id == 7) {
//                System.out.println(Arrays.toString(var2Val));
//            }
//            System.out.println(partition);
            filter |= propagate_SCC_Match();
            Measurer.matchingTime += System.nanoTime() - startTime;
//            System.out.println(Arrays.toString(var2Val));
//            if (id == 30 && numCall == 68)
//            if (id == 2 && numCall == 14)
//                System.out.println("after repair: " + Arrays.toString(var2Val));
//            if (id == 2 && numCall == 14)
//                System.out.println("after repair: " + partition);
//                System.out.println("after repair: " + Arrays.toString(var2Val));

            //build Graph
//            buildGraph();
            //filtering
            startTime = System.nanoTime();
            filter |= propagate_SCC_filter();
            Measurer.filterTime += System.nanoTime() - startTime;
//            if (id == 2 && numCall == 14)
//                System.out.println("final: " + partition);

//            printDoms();
        }

        return filter;
    }

    private boolean propagate_SCC_Match() throws ContradictionException {
        boolean res = false;
        IntVar x, y;
//        changedSCCs.clear();
        prepareForMatching();
        changedSCCStartIndex.clear();
        triggeringVars.iterateValid();
//        totalRepairMatchVarMask.clear();
//        TIntArrayList s;
//        TIntIterator iter;
        while (triggeringVars.hasNextValid()) {
            int xIdx = triggeringVars.next();
            int valIdx = var2Val[xIdx];
            int sccStartIdx = partition.getSCCStartIndexByElement(xIdx);
            x = vars[xIdx];

//            if (id == 7 && numCall == 43) {
//                System.out.println("propagate_SCC_Match: " + xIdx + ", valIdx: " + valIdx + ", ");
//            }

            if (valIdx == -1) {
//                repairMatchVarMask.clear();
//                partition.setIteratorIndex(sccStartIdx);
//                do {
//                    int i = partition.getValue();
//                    if (i < arity) {
//                        repairMatchVarMask.set(i);
////                        totalRepairMatchVarMask.set(i);
//                    }
//                } while (partition.nextValid());
//                prepareForMatching(repairMatchVarMask);
                repairMatching(sccStartIdx);
            }

            if (x.isInstantiated() && partition.partitionSize(sccStartIdx) > 2) {
                int xVal = vars[xIdx].getValue();

                if (changedSCCStartIndex.contains(sccStartIdx)) {
                    changedSCCStartIndex.remove(sccStartIdx);
                }

                //parition s into s1 s2 , from now on s = s2
//                System.out.println("partition remove: " + xIdx + " " + (val2Idx.get(xVal) + addArity));
//                System.out.println(partition);
                partition.remove(xIdx);
                partition.remove(val2Idx.get(xVal) + addArity);
//                System.out.println(xIdx + " is isInstantiated to: " + xVal);
//                System.out.println(partition);
                partition.setIteratorIndex(sccStartIdx);
                do {
                    int yIdx = partition.getValue();
                    if (yIdx < arity) {
                        y = vars[yIdx];
                        if (y.contains(xVal)) {
//                            System.out.println("remove: " + yIdx + ", " + xVal);
                            res |= y.removeValue(xVal, aCause);
//                            Dbit[yIdx].clear(val2Idx.get(xVal));
                        }
                    }
                } while (partition.nextValid());

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

    private boolean propagate_SCC_filter() throws ContradictionException {
        boolean filter = false;
//        resetData();
//        var iter = changedSCCStartIndex.iterator();
        changedSCCStartIndex.iterateValid();
        while (changedSCCStartIndex.hasNextValid()) {
//            buildGraph(iter.next(), restriction, unvisited, repairVars, repairVals);
//            if (id == 30 && numCall == 68)
//                System.out.println(partition);
            int sccStartIndex = changedSCCStartIndex.next();
            partition.getPartitionBitSetMaskAndVars(sccStartIndex, restriction, varsTmp, valsTmp, arity, numValues);
//            if (id == 2 && numCall == 14){
//                System.out.println(restriction);
//                System.out.println(varsTmp);
//            }
            resetData(restriction);
            findAllSCC(restriction, varsTmp);
//            if (id == 30 && numCall == 68)
//                System.out.println(partition);

            filter |= filterDomains(varsTmp);
        }
//        if (id == 30 && numCall == 68)
//            System.out.println(partition);
//        boolean filter = filterDomains();
        return filter;
    }

    private void prepareForMatching() {
        freeNode.fill();
        matchedValues.clear();
        varsTmp.clear();
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
                freeNode.remove(valIdx);
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
                        varsTmp.add(varIdx);
                    } else {
//                        freeNode.clear(oldMatchingIndex);
                        freeNode.remove(oldMatchingIndex);
                        matchedValues.set(oldMatchingIndex);
//                    System.out.println(oldMatchingIndex + " is free");
                    }
                } else {
                    varsTmp.add(varIdx);
                }

            }
        }
    }


    private void repairMatching(int SCCStartIndex) throws ContradictionException {
        // repair max matching.
        partition.setIteratorIndex(SCCStartIndex);
        do {
            int varIdx = partition.getValue();
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
                    Measurer.matchingTime += System.nanoTime() - startTime;
                    vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
                } else {
                    varsTmp.remove(varIdx);
                }
            }
        } while (partition.nextValid());
    }

    private void finalCheckAndRepairMatching() throws ContradictionException {
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
                Measurer.matchingTime += System.nanoTime() - startTime;
                vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
            }
        }
    }

    //***********************************************************************************
    // Initialization
    //***********************************************************************************

    private void MakeAugmentingPath(int start) {
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

//                    freeNode.clear(valIdx);
                    freeNode.remove(valIdx);
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
//                    System.out.println(num_to_visit + "," + next_node);
                    // 把这个变量加入队列中
                    visiting_[num_to_visit++] = next_node;
                    variable_visited_from_[next_node] = node;
//                    freeNode.clear(valIdx);
                    freeNode.remove(valIdx);
                    matchedValues.set(valIdx);
                }
            }
        }
    }

    private void findMaximumMatching() throws ContradictionException {
        freeNode.fill();
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
                freeNode.remove(valIdx);
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
//                        freeNode.clear(oldMatchingIndex);
                        freeNode.remove(oldMatchingIndex);
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
                Measurer.matchingTime += System.nanoTime() - startTime;
                vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
            }
        }

//        System.out.println(Arrays.toString(var2Val));
//        System.out.println(Arrays.toString(val2Var));
    }

    //***********************************************************************************
    // PRUNING
    //***********************************************************************************
//
//    private boolean filter() throws ContradictionException {
//        boolean filter = false;
//        findAllSCC();
////        System.out.println(Arrays.toString(varSCC));
////        System.out.println(Arrays.toString(valSCC));
//        for (int varIdx = 0; varIdx < arity; varIdx++) {
//            IntVar v = vars[varIdx];
//            if (!v.isInstantiated()) {
//                for (int k = v.getLB(), ub = v.getUB(); k <= ub; k = v.nextValue(k)) {
//                    int valIdx = val2Idx.get(k);
//                    if (varSCC[varIdx] != valSCC[valIdx]) {
//                        Measurer.enterP2();
//                        if (valIdx == var2Val[varIdx]) {
//                            int valNum = v.getDomainSize();
//                            Measurer.numDelValuesP2 += valNum - 1;
////                            System.out.println("instantiate  : " + v.getName() + ", " + k + " P2: " + Measurer.numDelValuesP2);
//                            filter |= v.instantiateTo(k, aCause);
//                        } else {
//                            ++Measurer.numDelValuesP2;
////                            System.out.println("second delete: " + v.getName() + ", " + k + " P2: " + Measurer.numDelValuesP2);
//                            filter |= v.removeValue(k, aCause);
//                        }
//                    }
//                }
//            }
//        }
//        return filter;
//    }


    private boolean filterDomains(SparseSet resVars) throws ContradictionException {
        boolean filter = false;
//        filterVars.iterateValid();
////        for (int varIdx = filterVars; varIdx < arity; varIdx++) {
//        while (filterVars.hasNextValid()) {
//            int varIdx = filterVars.next();
//        resVars.toBitSet(filterVars);
        resVars.iterateValid();
        while (resVars.hasNextValid()) {
            int varIdx = resVars.next();
//        for (int varIdx = filterVars.nextSetBit(0); varIdx >= 0 && varIdx < arity; varIdx = filterVars.nextSetBit(varIdx + 1)) {

//        }
            IntVar v = vars[varIdx];
//            if (id == 2 && numCall == 14)
//                System.out.println("filter var:" + v.getId());

            if (!v.isInstantiated()) {
                int ub = v.getUB();
                for (int k = v.getLB(); k <= ub; k = v.nextValue(k)) {
                    int valIdx = val2Idx.get(k);
//                    if (id == 2 && numCall == 14)
//                        System.out.println("filter val:" + k);
//                    if (node2SCC[varIdx] != node2SCC[valIdx + addArity]) {
                    if (!partition.inSameSCC(varIdx, valIdx + addArity)) {
                        Measurer.enterP2();
                        if (valIdx == var2Val[varIdx]) {
                            int valNum = v.getDomainSize();
                            Measurer.numDelValuesP2 += valNum - 1;
//                            if (id == 30 && numCall == 68)
//                            System.out.println("instantiate  : " + v.getId() + ", " + k + " P2: " + Measurer.numDelValuesP2);
//                            RDbit[varIdx].clear();
//                            RDbit[varIdx].set(valIdx);
//                            Dbit[varIdx].clear();
//                            Dbit[varIdx].set(valIdx);
                            filter |= v.instantiateTo(k, aCause);
                        } else {
                            ++Measurer.numDelValuesP2;
//                            if (id == 30 && numCall == 68)
//                            if (id == 2 && numCall == 14)
//                            System.out.println("propagate id: " + id + ", numcall:" + numCall + ", second delete: " + v.getId() + ", " + k + " P2: " + Measurer.numDelValuesP2);
//                            RDbit[varIdx].clear(valIdx);
//                            Dbit[varIdx].clear(valIdx);
                            filter |= v.removeValue(k, aCause);
                        }
                    }
                }
            }
        }
//        if (id == 30 && numCall == 68) {
//            printDoms();
//            System.out.println("final: " + filter);
//        }
        return filter;
    }
//
//    private void resetData() {
//        maxDFS = 0;
//        nbSCC = 0;
////        unconnected = false;
////        cycles.clear();
//
//        for (int i = 0; i < arity; i++) {
//            varLowLink[i] = Integer.MAX_VALUE;
//            varSCC[i] = -1;
//            varDFSNum[i] = Integer.MAX_VALUE;
//        }
//
//        for (int i = 0; i < numValues; i++) {
//            valLowLink[i] = Integer.MAX_VALUE;
//            valSCC[i] = -1;
//            valDFSNum[i] = Integer.MAX_VALUE;
//        }
//
//        sinkDFSNum = Integer.MAX_VALUE;
//        sinkLowLink = Integer.MAX_VALUE;
//        sinkIsInStack = false;
//        sinkIsUnvisited = true;
//
//        unVisitedVariables.set();
//        unVisitedValues.set();
////        singleton.clear();
//    }

    private void resetData(BitSet restrict) {
        maxDFS = 0;
//        nbSCC = 0;
//        unconnected = false;
//        cycles.clear();

        for (int i = restrict.nextSetBit(0); i >= 0 && i < arity; i = restriction.nextSetBit(i + 1)) {
            varLowLink[i] = Integer.MAX_VALUE;
//            varSCC[i] = -1;
            varDFSNum[i] = Integer.MAX_VALUE;
        }

        for (int i = restrict.nextSetBit(addArity); i > arity && i < numNodes; i = restrict.nextSetBit(i + 1)) {
            int j = totalIndex2ValIndex(i);
            valLowLink[j] = Integer.MAX_VALUE;
//            valSCC[j] = -1;
            valDFSNum[j] = Integer.MAX_VALUE;
        }

        if (restrict.get(arity)) {
            sinkDFSNum = Integer.MAX_VALUE;
            sinkLowLink = Integer.MAX_VALUE;
            sinkIsInStack = false;
            sinkIsUnvisited = true;
        }

        unVisitedVariables.set();
        unVisitedValues.set();
//        singleton.clear();
    }


//    private void findAllSCC() {
//        // initialization
//        clearVarStack();
//        clearValStack();
//
//        maxDFS = 0;
//        nbSCC = 0;
//
//        for (int i = 0; i < arity; i++) {
//            varLowLink[i] = Integer.MAX_VALUE;
//            varSCC[i] = -1;
//            varDFSNum[i] = Integer.MAX_VALUE;
//        }
//
//        for (int i = 0; i < numValues; i++) {
//            valLowLink[i] = Integer.MAX_VALUE;
//            valSCC[i] = -1;
//            valDFSNum[i] = Integer.MAX_VALUE;
//        }
//
//        sinkDFSNum = Integer.MAX_VALUE;
//        sinkLowLink = Integer.MAX_VALUE;
//        sinkIsInStack = false;
//        sinkIsUnvisited = true;
//
//        unVisitedVariables.set();
//        unVisitedValues.set();
//
//        findSingletons();
////        singleton.flip();
////        System.out.println("----------");
////        System.out.println("singleton:" + singleton);
////        System.out.println("singleton: " + singleton);
//        for (int varIdx = restriction.nextSetBit(0); varIdx > 0 && varIdx < arity; varIdx = restriction.nextSetBit(varIdx + 1)) {
////            if (unVisitedVariables.get(varIdx)) {
////                System.out.println(varIdx);
////            System.out.printf("out: %d\n", varIdx);
//            strongConnectVar(varIdx);
////            }
//        }
//
////        System.out.println(Arrays.toString(varSCC));
////        System.out.println(Arrays.toString(valSCC));
//    }

    boolean findAllSCC(BitSet restri, SparseSet resVars) {
        clearVarStack();
        clearValStack();

        findSingletons(restri, resVars);
//        System.out.println("restriction: " + restri);
//        System.out.println("partition: " + partition);
        for (int varIdx = restri.nextSetBit(0); varIdx >= 0 && varIdx < arity; varIdx = restriction.nextSetBit(varIdx + 1)) {
//            if (unVisitedVariables.get(varIdx)) {
//                System.out.println(varIdx);
//            System.out.printf("out: %d\n", varIdx);
            strongConnectVar(varIdx);
//            }
        }
        return false;
    }

    private void findSingletons(BitSet restri, SparseSet resVars) {
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
                restri.clear(i);
                restri.clear(var2Val[i]);
                partition.remove(i);
                partition.remove(var2Val[i]);
//                nbSCC++;
            }
        }
    }

    private void strongConnectVar(int curNode) {
//        System.out.println("scvr: " + curNode);
        pushVarStack(curNode);
        varDFSNum[curNode] = maxDFS;
        varLowLink[curNode] = maxDFS;
        maxDFS++;
        unVisitedVariables.clear(curNode);

        int matchedVal = var2Val[curNode];
        IntVar v = vars[curNode];
        for (int a = v.getLB(), ub = v.getUB(); a <= ub; a = v.nextValue(a)) {
            int newNode = val2Idx.get(a);
            if (newNode == matchedVal) continue;
//            System.out.println("scVartoVal: " + curNode + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
//            System.out.println(curNode + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
            if (!unVisitedValues.get(newNode)) {
                if (valIsInStack.get(newNode)) {
                    varLowLink[curNode] = Math.min(varLowLink[curNode], valDFSNum[newNode]);
                }
            } else {
                strongConnectVal(newNode);
                varLowLink[curNode] = Math.min(varLowLink[curNode], valLowLink[newNode]);
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
    }

    private void strongConnectVal(int curNode) {
//        System.out.println("scvl: " + curNode);
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
                }
            } else {
                strongConnectSink();
                valLowLink[curNode] = Math.min(valLowLink[curNode], sinkLowLink);
            }
        }
//        System.out.println(curNode + " has no nei " + lowLink[curNode] + ", " + DFSNum[curNode]);
        if (valLowLink[curNode] == valDFSNum[curNode]) {
            if (valLowLink[curNode] > 0 || valIsInStack.size() + varIsInStack.size() > 0) {
                hasSCCSplit = true;
            }
            if (hasSCCSplit) {
//                int stackNode = -1;
//                sccSize = 0;
//                while (stackNode != curNode) {
//                    stackNode = popValStack();
////                    System.out.println("pop: " + stackNode + ", " + nbSCC);
//                    valSCC[stackNode] = nbSCC;
//                    sccSize++;
//                    varSCC[popVarStack()] = nbSCC;
//                    sccSize++;
//                }
////                if (sccSize == 1) {
////                    singleton.add(nbSCC);
////                }
//                nbSCC++;
                processSCC(valDFSNum[curNode]);
            }
        }
//        System.out.println("back");
    }

    private void strongConnectSink() {
//        System.out.println("scs: ");
        sinkIsInStack = true;
        sinkDFSNum = maxDFS;
        sinkLowLink = maxDFS;
        maxDFS++;
        sinkIsUnvisited = false;
//        Iterator<Integer> iterator = graph.getSuccOf(curNode).iterator();
//        while (iterator.hasNext()) {
//            int newNode = iterator.next();
////            System.out.println(curNode + ", " + newNode + ", " + unvisited.get(newNode));
//            if (!unvisited.get(newNode)) {
//                if (inStack.get(newNode)) {
//                    lowLink[curNode] = Math.min(lowLink[curNode], DFSNum[newNode]);
//                }
//            } else {
//                strongConnectR(newNode);
//                lowLink[curNode] = Math.min(lowLink[curNode], lowLink[newNode]);
//            }
//        }

        for (int newNode = matchedValues.firstSetBit(); newNode != matchedValues.end(); newNode = matchedValues.nextSetBit(newNode + 1)) {
//            System.out.println("scSinktoVal: " + arity + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
//            System.out.println(arity + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
            if (!unVisitedValues.get(newNode)) {
                if (valIsInStack.get(newNode)) {
                    sinkLowLink = Math.min(sinkLowLink, valDFSNum[newNode]);
                }
            } else {
                strongConnectVal(newNode);
                sinkLowLink = Math.min(sinkLowLink, valLowLink[newNode]);
            }
        }

//        long values = 0;
//        int newNode = 0, iBase = 0;
//        int i = 0;
//        for (int iWord = matchedValues.firstSetBit(); iWord <= matchedValues.lastSetIndex(); ++iWord) {
//            values = matchedValues.getWord(iWord) & ~unVisitedValues.getWord(iWord) & valIsInStack.getWord(iWord);
//            iBase = iWord * 64;
//            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
//                newNode = iBase + i;
//                sinkLowLink = Math.min(sinkLowLink, valDFSNum[newNode]);
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

//        System.out.println(curNode + " has no nei " + lowLink[curNode] + ", " + DFSNum[curNode]);
        if (sinkLowLink == sinkDFSNum) {
            if (sinkLowLink > 0 || sinkIsInStack || valIsInStack.size() + varIsInStack.size() > 0) {
                hasSCCSplit = true;
            }
            if (hasSCCSplit) {
                processSCC(sinkDFSNum);
            }
        }
//        System.out.println("back");
    }

    private void processSCC(int rootNum) {
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
//        nbSCC++;
    }

    private void pushVarStack(int v) {
        varStack[varStackIdx++] = v;
        varIsInStack.set(v);
    }

    private void clearVarStack() {
        varIsInStack.clear();
        varStackIdx = 0;
    }

    private int popVarStack() {
        int x = varStack[--varStackIdx];
        varIsInStack.clear(x);
        return x;
    }

    private void pushValStack(int v) {
        valStack[valStackIdx++] = v;
        valIsInStack.set(v);
    }

    private void clearValStack() {
        valIsInStack.clear();
        valStackIdx = 0;
    }

    private int popValStack() {
        int x = valStack[--valStackIdx];
        valIsInStack.clear(x);
        return x;
    }

    public int nextSetBit(long words, int bitIndex) {
        return Long.numberOfTrailingZeros(words & -1L << bitIndex);
    }

    private int getTopVarStack() {
        return varStack[varStackIdx - 1];
    }

    private int getTopValStack() {
        return valStack[valStackIdx - 1];
    }

    int totalIndex2ValIndex(int totalIndex) {
        return totalIndex - addArity;
    }

    int valIndex2TotalIndex(int valIndex) {
        return valIndex + addArity;
    }
//    boolean isEqual(BitSet a,SparseSet b){
//        b.iterateValid();
//        while (b.hasNextValid()){}
//    }
}