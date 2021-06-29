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
public class AlgoAllDiffAC_WordRamGent {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************
    // 约束的个数
    static public int num = 0;

    // 约束的编号
    protected int id;
    protected long numCall = -1;

    protected int arity;
    protected IntVar[] vars;
    protected ICause aCause;

    // 新增一点（视为变量）
    protected int addArity;

    // 自由值集合
    protected SparseSet freeNode;

    // 以下是bit版本所需数据结构========================
    // numValue是二部图中取值编号的个数，numBit是二部图的最大边数
    protected int numValues;

    protected int numNodes;
    // 值到索引
    protected int[] idx2Val;
    // 索引到值
    protected TIntIntHashMap val2Idx;

    // 与值相连的变量
    protected INaiveBitSet[] B;
    protected INaiveBitSet[] D;

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

    long startTime;
    //
    IEnvironment env;

    // for bit DFS Tarjan

    //栈
    protected int[] varStack;
    protected int[] valStack;
    protected INaiveBitSet varIsInStack;
    protected INaiveBitSet valIsInStack;
    int varStackIdx;
    int valStackIdx;

    protected int maxDFS = 1;
    protected int[] varDFSNum;
    protected int[] valDFSNum;
    protected int[] varLowLink;
    protected int[] valLowLink;
    protected boolean hasSCCSplit = false;

    int sinkDFSNum;
    int sinkLowLink;
    boolean sinkIsInStack;
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

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_WordRamGent(IntVar[] variables, ICause cause, Model model) {
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

        freeNode = new SparseSet(numValues);

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
    }

    protected UnaryIntProcedure<Integer> makeProcedure() {
        return new UnaryIntProcedure<Integer>() {
            int var;
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
            startTime = System.nanoTime();
            findMaximumMatching();
            Measurer.matchingTime += System.nanoTime() - startTime;
            // filtering
            startTime = System.nanoTime();
            resetData(varsTmp, valsTmp, true);
            findAllSCC(restriction, varsTmp);
            filter = filterDomains(varsTmp, valsTmp);
            Measurer.filterTime += System.nanoTime() - startTime;
        } else {
            // initial
            triggeringVars.clear();
            for (int i = 0; i < arity; ++i) {
                monitors[i].freeze();
                monitors[i].forEachRemVal(onValRem.set(i));
                monitors[i].unfreeze();
            }

            //matching
            startTime = System.nanoTime();
            filter |= propagate_SCC_Match();
            Measurer.matchingTime += System.nanoTime() - startTime;
            //filtering
            startTime = System.nanoTime();
            filter |= propagate_SCC_filter();
            Measurer.filterTime += System.nanoTime() - startTime;
        }

        return filter;
    }

    protected boolean propagate_SCC_Match() throws ContradictionException {
        boolean res = false;
        IntVar x, y;
        prepareForMatching();
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

    protected boolean propagate_SCC_filter() throws ContradictionException {
        boolean filter = false;
        changedSCCStartIndex.iterateValid();
        while (changedSCCStartIndex.hasNextValid()) {
            int sccStartIndex = changedSCCStartIndex.next();
            partition.getPartitionBitSetMaskAndVars(sccStartIndex, restriction, varsTmp, valsTmp, arity, numNodes);
            resetData(varsTmp, valsTmp, restriction.get(arity));
            findAllSCC(restriction, varsTmp);
            filter |= filterDomains(varsTmp, valsTmp);
        }
        return filter;
    }

    protected void prepareForMatching() {
        freeNode.fill();
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
                freeNode.remove(valIdx);
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
                        freeNode.remove(oldMatchingIndex);
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
//                    Measurer.matchingTime += System.nanoTime() - startTime;
                    vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
                } else {
                    varsTmp.remove(varIdx);
                }
            }
        } while (partition.nextValid());
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

    protected void findMaximumMatching() throws ContradictionException {
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
        boolean filter = false;
        filterVars.iterateValid();
        while (filterVars.hasNextValid()) {
            int varIdx = filterVars.next();
            IntVar v = vars[varIdx];
            if (!v.isInstantiated()) {
                filterVals.iterateValid();
                while (filterVals.hasNextValid()) {
                    int valIdx = filterVals.next();
                    int k = idx2Val[valIdx];
//                int ub = v.getUB();
//                for (int k = v.getLB(); k <= ub; k = v.nextValue(k)) {
//                    int valIdx = val2Idx.get(k);
                    if (!partition.inSameSCC(varIdx, valIdx + addArity)) {
                        Measurer.enterP2();
                        if (valIdx == var2Val[varIdx]) {
                            int valNum = v.getDomainSize();
                            Measurer.numDelValuesP2 += valNum - 1;
                            filter |= v.instantiateTo(k, aCause);
                        } else {
                            ++Measurer.numDelValuesP2;
                            filter |= v.removeValue(k, aCause);
                        }
                    }
                }
            }
        }
        return filter;
    }

    protected void resetData(SparseSet resetVars, SparseSet resetVals, boolean containsSink) {
        maxDFS = 0;

        resetVars.iterateValid();
        while (resetVars.hasNextValid()) {
            int i = resetVars.next();
            varLowLink[i] = Integer.MAX_VALUE;
            varDFSNum[i] = Integer.MAX_VALUE;
        }

        resetVals.iterateValid();
        while (resetVals.hasNextValid()) {
            int i = resetVals.next();
            valLowLink[i] = Integer.MAX_VALUE;
            valDFSNum[i] = Integer.MAX_VALUE;
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
                restri.clear(i);
                restri.clear(var2Val[i]);
                partition.remove(i);
                partition.remove(var2Val[i]);
//                nbSCC++;
            }
        }
    }

    protected void strongConnectVar(int curNode) {
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

    protected void strongConnectVal(int curNode) {
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

    protected void strongConnectSink() {
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
//    boolean isEqual(BitSet a,SparseSet b){
//        b.iterateValid();
//        while (b.hasNextValid()){}
//    }
}