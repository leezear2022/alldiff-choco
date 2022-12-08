package org.chocosolver.solver.constraints.nary.alldifferent.algo;

//import org.chocosolver.amtf.Measurer;

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.list.array.TIntArrayList;
import gnu.trove.list.array.TLongArrayList;
import gnu.trove.map.hash.TIntIntHashMap;
import gnu.trove.stack.array.TLongArrayStack;
import org.chocosolver.memory.IEnvironment;
import org.chocosolver.memory.IStateBitSet;
import org.chocosolver.memory.IStateInt;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
import org.chocosolver.util.iterators.DisposableValueIterator;
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
public class AlgoAllDiffAC20 extends AlgoAllDiffAC_Simple {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************

    // 约束的编号
//    protected long numCall = -1;

//    protected int arity;
//    protected IntVar[] vars;
//    protected ICause aCause;

    // 新增一点（视为变量）
    protected int addArity;

    // if all a in var x val2Idx[a] = a then DomIsRagular[x] = true
    boolean[] domIsRegular;

    protected IStateBitSet matchedValuesR;
    protected IStateBitSet validValuesR;
    protected IStateBitSet freeNodesR;
    protected IStateInt[] var2ValR;
    protected IStateInt[] val2VarR;
    protected IStateInt[] numRB;
    protected BitSet visitedValues;

    // 自由值集合
//    protected SparseSet freeNode;

    // 以下是bit版本所需数据结构========================
    // numValue是二部图中取值编号的个数，numBit是二部图的最大边数
//    protected int numValues;

    protected int numNodes;
    // 值到索引
//    protected int[] idx2Val;
    // 索引到值
//    protected TIntIntHashMap val2Idx;

    // 与值相连的变量
//    protected INaiveBitSet[] B;
//    protected INaiveBitSet[] D;

    // 已访问过的变量和值
    protected INaiveBitSet unVisitedVariables;
//    protected INaiveBitSet unVisitedValues;
//    protected INaiveBitSet matchedValues;

    // matching
//    protected int[] val2Var;
//    protected int[] var2Val;

    // 记录队列
    protected int[] visiting_;
    protected int[] variable_visited_from_;
    protected long startTime;
    //
//    IEnvironment env;

    // for bit DFS Tarjan

    //栈
    protected int[] varStack;
    protected int[] valStack;
    protected INaiveBitSet varIsInStack;
    protected INaiveBitSet valIsInStack;
    int varStackIdx;
    int valStackIdx;

    protected int maxDFS = 0;
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
    protected IStateBitSet activeVars;
    protected SparseSet changedSCCStartIndex;
    protected SparseSet varsTmp;
    protected SparseSet valsTmp;

    protected boolean initialPropagation = true;
    private TIntArrayList[] deletedValues;
    private TLongArrayStack DE;
    private TLongArrayList cycles;
    protected boolean unconnected = false;
    private IntPair nodePair;
    private static int INT_SIZE = 32;
    protected boolean isSkiped = false;
    private INaiveBitSet unVisitedValues;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC20(IntVar[] variables, ICause cause, Model model) {
        super(variables, cause, model.getEnvironment());
        id = num++;
        addArity = arity + 1;
        numNodes = addArity + numValues;

        // initial numRB
        numRB = new IStateInt[numValues];
        for (int i = 0; i < numValues; i++) {
            numRB[i] = env.makeInt(0);
        }

        for (int i = 0; i < arity; ++i) {
            IntVar v = vars[i];
            for (int val = v.getLB(), ub = v.getUB(); val <= ub; val = v.nextValue(val)) {
                // 值+1 numRB[a]++;
                int valIdx = val2Idx.get(val);
                numRB[valIdx].set(numRB[valIdx].get() + 1);
            }
        }

        // initial domIsRegular
        domIsRegular = new boolean[arity];
        for (int i = 0; i < arity; ++i) {
            domIsRegular[i] = isRegular(vars[i]);
        }

        // 记录访问过的变量
        visiting_ = new int[arity];
        unVisitedVariables = INaiveBitSet.makeBitSet(arity, true);
        // 变量的前驱变量，若前驱变量是-1，则表示无前驱变量，就是第一个变量
        variable_visited_from_ = new int[arity];
        unVisitedValues = INaiveBitSet.makeBitSet(numValues, true);
//        unMatchedValues = INaiveBitSet.makeBitSet(numValues, true);
//        matchedValues = INaiveBitSet.makeBitSet(numValues, false);
        visitedValues = new BitSet(numValues);
        matchedValuesR = env.makeBitSet(numValues);
        validValuesR = env.makeBitSet(numValues);
//        A = new SimpleBitSet(numValues);
//        fn = new SimpleBitSet(numValues);
        freeNodesR = env.makeBitSet(numValues);

        for (int i = 0; i < numValues; i++) {
            validValuesR.set(i);
            freeNodesR.set(i);
        }

        var2ValR = new IStateInt[arity];
        val2VarR = new IStateInt[numValues];

        for (int i = 0; i < arity; ++i) {
            var2ValR[i] = env.makeInt(-1);
        }
        for (int i = 0; i < numValues; ++i) {
            val2VarR[i] = env.makeInt(-1);
        }

        // for bit DFS
        varStack = new int[arity];
        valStack = new int[numValues];

        varIsInStack = INaiveBitSet.makeBitSet(arity, false);
        valIsInStack = INaiveBitSet.makeBitSet(numValues, false);

        varDFSNum = new int[arity];
        valDFSNum = new int[numValues];
        varLowLink = new int[arity];
        valLowLink = new int[numValues];

        // for Gent algorithm
        partition = new RSetPartition(addArity + numValues, env);
        restriction = new BitSet(addArity + numValues);
        triggeringVars = new SparseSet(arity);
        activeVars = env.makeBitSet(arity);
        activeVars.set(0, arity);
        changedSCCStartIndex = new SparseSet(numNodes);
        varsTmp = new SparseSet(arity);
        valsTmp = new SparseSet(numValues);

        monitors = new IIntDeltaMonitor[vars.length];
        for (int i = 0; i < vars.length; i++) {
            monitors[i] = vars[i].monitorDelta(cause);
        }
        onValRem = makeProcedure();
        // for zhang20
        DE = new TLongArrayStack();
        deletedValues = new TIntArrayList[arity];
        for (int i = 0; i < arity; i++) {
            deletedValues[i] = new TIntArrayList(numValues);
        }
        cycles = new TLongArrayList(numNodes);
        nodePair = new IntPair(-1, -1);
    }

    protected boolean isRegular(IntVar v) {
        for (int val = v.getLB(), ub = v.getUB(); val <= ub; val = v.nextValue(val))
            if (val != val2Idx.get(val))
                return false;
        return true;
    }

    protected UnaryIntProcedure<Integer> makeProcedure() {
        return new UnaryIntProcedure<Integer>() {
            int varIdx;
            // boolean isNotTrigger;
            IntVar v;
            int matchedVal = -1;
            boolean isReg;

            @Override
            public UnaryIntProcedure set(Integer o) {
                varIdx = o;
                v = vars[varIdx];
                matchedVal = var2ValR[varIdx].get();
                isReg = domIsRegular[varIdx];
                return this;
            }

            @Override
            public void execute(int i) {
                int valIdx = isReg ? i : val2Idx.get(i);

                // 删的值是匹配值，清理匹配
                if (valIdx == matchedVal) {
                    var2ValR[varIdx].set(-1);
                    val2VarR[valIdx].set(-1);
                    matchedValuesR.clear(valIdx);
                    freeNodesR.set(valIdx);
                }

                deletedValues[varIdx].add(valIdx);
                numRB[valIdx].set(numRB[valIdx].get() - 1);

                // belong 删空表示该值失效，不再参与过滤
                if (numRB[valIdx].get() == 0) {
                    validValuesR.clear(valIdx);
                    freeNodesR.clear(valIdx);
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
        isSkiped = false;
        ++numCall;
        boolean filter = false;
        Measurer.enterProp();

        if (initialPropagation) {
            // initial
            restriction.set(0, numNodes);
            varsTmp.fill();
            // matching
            startTime = System.nanoTime();
            deltaUpdate();
            findMaximumMatching();
            Measurer.matchingTime += System.nanoTime() - startTime;
            // filtering
            startTime = System.nanoTime();
            resetData(varsTmp, valsTmp, true);

            findAllSCC(restriction, varsTmp);
            filter = filterDomains(varsTmp, valsTmp);
            Measurer.filterTime += System.nanoTime() - startTime;
            initialPropagation = false;
        } else {
            //matching
            startTime = System.nanoTime();
            deltaUpdate();
            filter |= propagate_SCC_Match();
            Measurer.matchingTime += System.nanoTime() - startTime;
            //filtering
            startTime = System.nanoTime();
            filter |= propagate_SCC_filter();
            Measurer.filterTime += System.nanoTime() - startTime;
        }

        if (isSkiped) {
            Measurer.enterSkip();
        }

        return filter;
    }

    @Override
    protected void removeValueR(int varIdx, int valIdx) {

    }

    @Override
    protected void instantiateToR(int varIdx, int valIdx) {

    }

    protected boolean propagate_SCC_Match() throws ContradictionException {
        boolean res = false;
        IntVar x, y;
        // 匹配值清空
        changedSCCStartIndex.clear();
        triggeringVars.iterateValid();
        while (triggeringVars.hasNextValid()) {
            int xIdx = triggeringVars.next();
            int valIdx = var2ValR[xIdx].get();

            int sccStartIdx = partition.getSCCStartIndexByElement(xIdx);
            x = vars[xIdx];

            if (valIdx == -1 || x.contains(idx2Val[valIdx])) {
                repairMatching(sccStartIdx);
            }

            if (x.isInstantiated() && partition.partitionSize(sccStartIdx) > 2) {
                valIdx = var2ValR[xIdx].get();
                int xVal = idx2Val[valIdx];
                if (changedSCCStartIndex.contains(sccStartIdx)) {
                    changedSCCStartIndex.remove(sccStartIdx);
                }

                //parition s into s1 s2 , from now on s = s2
                partition.remove(xIdx);
                partition.remove(var2ValR[xIdx].get() + addArity);

                partition.setIteratorIndexBySCCStartIndex(sccStartIdx);
                do {
                    int yIdx = partition.getValid();
                    if (yIdx < arity) {
                        y = vars[yIdx];
                        if (y.contains(xVal)) {
//                            System.out.println("remove: " + yIdx + ", " + xVal);
                            res |= y.removeValue(xVal, aCause);
                            // !! 这里的删值 没入deleteedge队列
//                            Dbit[yIdx].clear(val2Idx.get(xVal));
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
        return res;
    }

    protected boolean propagate_SCC_filter() throws ContradictionException {
        boolean filter = false;
        maxDFS = 0;
        unconnected = false;
        cycles.clear();
        changedSCCStartIndex.iterateValid();
        while (changedSCCStartIndex.hasNextValid()) {
            int sccStartIndex = changedSCCStartIndex.next();
            partition.getPartitionBitSetMaskAndVars(sccStartIndex, restriction, varsTmp, valsTmp, arity, numNodes);
            resetData(varsTmp, valsTmp, restriction.get(arity));
//            System.out.println("valDFSNum: " + Arrays.toString(valDFSNum) + ", " + restriction + "," + partition);
            findAllSCC(restriction, varsTmp);
            filter |= filterDomains(varsTmp, valsTmp);
        }
        return filter;
    }

    protected void repairMatching(int SCCStartIndex) throws ContradictionException {
        // repair max matching.
        partition.setIteratorIndexBySCCStartIndex(SCCStartIndex);
        do {
            int varIdx = partition.getValid();
//            if (id == 7) {
//                System.out.print(varIdx + " ");
//            }
            if (varIdx < arity) {
//                if (var2Val[varIdx] == -1) {
                int valIdx = var2ValR[varIdx].get();
                if (valIdx == -1 || !vars[varIdx].contains(idx2Val[valIdx])) {
                    var2ValR[varIdx].set(-1);
                    visitedValues.clear();
                    unVisitedVariables.set();
                    MakeAugmentingPath(varIdx);
                }

                //匹配失败退出
                if (var2ValR[varIdx].get() == -1) {
                    vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
                }
            }
        } while (partition.goToNextValid());
    }

    //***********************************************************************************
    // Initialization
    //***********************************************************************************

    private void deltaUpdate() throws ContradictionException {
        // 触发队列和更新队列
        triggeringVars.clear();
//        updatedVars.clear();
//        updatedVals.clear();

//        for (int varIdx = 0; varIdx < arity; varIdx++) {
        for (int varIdx = activeVars.nextSetBit(0); varIdx >= 0; varIdx = activeVars.nextSetBit(varIdx + 1)) {
            monitors[varIdx].freeze();
            int numDeltaSize = monitors[varIdx].sizeApproximation();
            if (numDeltaSize != 0) {
                // 变量发生改变
                deletedValues[varIdx].clear();
                triggeringVars.add(varIdx);
                // 只动变量论域改变的变量，触发变量和删值队列都更新一下
                monitors[varIdx].forEachRemVal(onValRem.set(varIdx));
//                RD[varIdx].generateBitSet(D[varIdx]);
//                updatedVars.add(varIdx);
            }
            monitors[varIdx].unfreeze();

            if (vars[varIdx].isInstantiated()) {
                activeVars.clear(varIdx);
            }
        }
    }

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
            boolean isReg = domIsRegular[node];
            for (int value = v.getLB(), ub = v.getUB(); value <= ub; value = v.nextValue(value)) {
                int valIdx = isReg ? value : val2Idx.get(value);
                if (visitedValues.get(valIdx)) continue;
                visitedValues.set(valIdx);

//                int valIdx = val2Idx.get(value);
//                if (!unVisitedValues.get(valIdx)) continue;
//                unVisitedValues.clear(valIdx);
//                if (!matchedValues.get(valIdx)) {
                if (!matchedValuesR.get(valIdx)) {
                    int path_node = node;
                    int path_value = valIdx;
                    while (path_node != -1) {
                        // 旧变量拿到旧匹配值
                        int old_value = var2ValR[path_node].get();
                        // 旧变量拿到新匹配值
                        var2ValR[path_node].set(path_value);
                        val2VarR[path_value].set(path_node);

                        // 回溯到上一个变量
                        path_node = variable_visited_from_[path_node];
                        // 由于这个变量传递下去是连贯的，可以检查连通生，做为下一个阶段的记录
                        path_value = old_value;
                    }

                    freeNodesR.clear(valIdx);
                    matchedValuesR.set(valIdx);
//                    System.out.println(valIdx + " is not free");
                    return;
                } else {
                    // Enqueue node matched to valIdx.
                    // 若没有该值已经有匹配，但变量没有匹配

                    // 先拿到这个值的匹配变量
//                    int next_node = val2Var[valIdx];
                    int next_node = val2VarR[valIdx].get();
//                    variable_visited_.set(next_node);
                    unVisitedVariables.clear(next_node);
//                    System.out.println(num_to_visit + "," + next_node);
                    // 把这个变量加入队列中
                    visiting_[num_to_visit++] = next_node;
                    variable_visited_from_[next_node] = node;
                    freeNodesR.clear(valIdx);
//                    freeNode.remove(valIdx);
                    matchedValuesR.set(valIdx);
                }
            }
        }
    }

    private void findMaximumMatching() throws ContradictionException {
//        // !! 可做增量
//        freeNode.fill();
        for (int varIdx = 0; varIdx < arity; varIdx++) {
//            for (int varIdx = activeVars.nextSetBit(0); varIdx >=0 ; varIdx = activeVars.nextSetBit(varIdx + 1)) {
            if (var2ValR[varIdx].get() == -1) {
                visitedValues.clear();
                unVisitedVariables.set();
                MakeAugmentingPath(varIdx);
            }
            if (var2ValR[varIdx].get() == -1) {
                // No augmenting path exists.
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
                        if (valIdx == var2ValR[varIdx].get()) {
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
//        maxDFS = 0;
//        cycles.clear();
        DE.clear();
        hasSCCSplit = false;

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
                int totalIdx = valIndex2TotalIndex(var2ValR[i].get());
                restri.clear(i);
                restri.clear(totalIdx);
                partition.remove(i);
                partition.remove(totalIdx);
//                nbSCC++;
            }
        }
    }

    protected void strongConnectVar(int curNode) {
//        System.out.println("scvr: " + curNode + ", " + maxDFS);
        pushVarStack(curNode);
        varDFSNum[curNode] = maxDFS;
        varLowLink[curNode] = maxDFS;
        maxDFS++;
        unVisitedVariables.clear(curNode);

        int matchedVal = var2ValR[curNode].get();
        IntVar v = vars[curNode];
        for (int a = v.getLB(), ub = v.getUB(); a <= ub; a = v.nextValue(a)) {
            int newNode = val2Idx.get(a);
            if (newNode == matchedVal) continue;
//            System.out.println("scVartoVal: " + curNode + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
//            System.out.println(curNode + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
            if (!unVisitedValues.get(newNode)) {
                if (valIsInStack.get(newNode)) {
                    varLowLink[curNode] = Math.min(varLowLink[curNode], valDFSNum[newNode]);
                    if (numCall != 0 && DE.size() != 0 && !unconnected) DETest(valLowLink[newNode], maxDFS - 1);
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

        if (numCall != 0 && !unconnected && (DE.size() == 0)) {
//            System.out.println("xixi");
            isSkiped = true;
            return;
        }
    }

    protected void strongConnectVal(int curNode) {
//        System.out.println("scvl: " + curNode + ", " + maxDFS);
        pushValStack(curNode);
        valDFSNum[curNode] = maxDFS;
        valLowLink[curNode] = maxDFS;
        maxDFS++;
        unVisitedValues.clear(curNode);
        int matchedVar = val2VarR[curNode].get();
        if (matchedVar != -1) {
            //have matched variable
//            System.out.println("scValtoVar: " + (addArity + curNode) + ", " + matchedVar + ", " + unVisitedVariables.get(matchedVar));
//            System.out.println((addArity + curNode) + ", " + matchedVar + ", " + unVisitedVariables.get(matchedVar));
            if (!unVisitedVariables.get(matchedVar)) {
                if (varIsInStack.get(matchedVar)) {
                    valLowLink[curNode] = Math.min(valLowLink[curNode], varDFSNum[matchedVar]);
                    if (numCall != 0 && DE.size() != 0 && !unconnected) DETest(varLowLink[matchedVar], maxDFS - 1);
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
                    if (numCall != 0 && DE.size() != 0 && !unconnected) DETest(sinkLowLink, maxDFS - 1);
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

        if (numCall != 0 && !unconnected && (DE.size() == 0)) {
//            System.out.println("xixi");
            isSkiped = true;
            return;
        }
    }

    protected void strongConnectSink() {
//        System.out.println("scs: " + ", " + maxDFS);
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

        for (int newNode = matchedValuesR.nextSetBit(0); newNode >= 0; newNode = matchedValuesR.nextSetBit(newNode + 1)) {
//            System.out.println("scSinktoVal: " + arity + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
//            System.out.println(arity + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
            if (!unVisitedValues.get(newNode)) {
                if (valIsInStack.get(newNode)) {
                    sinkLowLink = Math.min(sinkLowLink, valDFSNum[newNode]);
                    if (numCall != 0 && DE.size() != 0 && !unconnected) DETest(valLowLink[newNode], maxDFS - 1);
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

        if (numCall != 0 && !unconnected && (DE.size() == 0)) {
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
//
//    public int nextSetBit(long words, int bitIndex) {
//        return Long.numberOfTrailingZeros(words & -1L << bitIndex);
//    }

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


//    private void DETest(int lowLinkNewNode, int dfs) {
////        System.out.println("DETest: " + lowLinkNewNode + ", " + dfs + " unconnected: " + unconnected + " DE Size: " + DE.size());
//        if (!unconnected) {
//            cycles.add(lowLinkNewNode, dfs);
//
//            while (!(DE.size() == 0) && inCycles(DE.peek())) {
//                DE.pop();
//            }
//        }
//    }

    private void DETest(int lowLinkNewNode, int dfs) {
//        System.out.println("DETest: " + lowLinkNewNode + ", " + dfs + " unconnected: " + unconnected + " DE Size: " + DE.size());
        addCycles(getIntTuple2Long(lowLinkNewNode, dfs));
        while (!(DE.size() == 0) && inCycles(DE.peek())) {
            DE.pop();
        }
    }

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

        for (int i = 0, len = cycles.size(); i < len; ++i) {
            long e = cycles.get(i);
            if (cover(e, a, b)) {
                return true;
            }
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