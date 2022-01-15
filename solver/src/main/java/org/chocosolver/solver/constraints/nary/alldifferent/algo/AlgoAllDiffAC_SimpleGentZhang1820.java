package org.chocosolver.solver.constraints.nary.alldifferent.algo;

//import org.chocosolver.amtf.Measurer;

import gnu.trove.list.array.TIntArrayList;
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

import java.util.Arrays;
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
public class AlgoAllDiffAC_SimpleGentZhang1820 extends AlgoAllDiffAC_Simple {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************
    // 已访问过的变量和值
    private SimpleBitSet unVisitedVariables;
    private BitSet visitedValues;
    // matching
    private IStateInt[] val2VarR;
    private IStateInt[] var2ValR;
    // 记录队列
    private int[] visiting_;
    private int[] variable_visited_from_;

    // 变量到变量的连通性
    // 对于惰性算法，记录是否知道-变量到变量的连通性
    private SimpleBitSet[] graphLinkedMatrix;
    private SimpleBitSet[] graphLinkedFrontier;

    // !! 记录gamma的前沿
    private SimpleBitSet gammaFrontier;
    // 记录gamma的bitset
    private SimpleBitSet gammaMask;

    // 记录scc
    protected boolean initialPropagation = true;
    protected IStatePartition partition;
    private SparseSet triggeringVars;
    //    private SparseSet triggeringVals;
    private IIntDeltaMonitor[] monitors;
    private UnaryIntProcedure<Integer> onValRem;
    private SparseSet[] deletedValues;
    protected SparseSet varsTmp;
    private SparseSet changedSCCStartIndex;
    protected boolean unconnected = false;
    protected boolean isSkiped = false;

    long startTime;

    IStateBitSet[] RB;
    IStateBitSet[] RD;
    // if all a in var x val2Idx[a] = a then DomIsRagular[x] = true
    boolean[] domIsRegular;

    // for Zhang18
    private IStateBitSet matchedValuesR;
    private IStateBitSet validValuesR;
    private SimpleBitSet A;
    private final IStateBitSet freeNodesR;

    // for early detect
    private TIntArrayList sccTriggeringVars;
    private int numSCCDeleteValues;
    private int numSCCValues;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_SimpleGentZhang1820(IntVar[] variables, ICause cause, Model model) {
        super(variables, cause, model.getEnvironment());
        id = num++;
//        System.out.println("id: " + id + " Zhang1820");
        RB = new IStateBitSet[numValues];
        for (int i = 0; i < numValues; ++i) {
            RB[i] = env.makeBitSet(arity);
        }

        RD = new IStateBitSet[arity];
        domIsRegular = new boolean[arity];
        for (int i = 0; i < arity; i++) {
            RD[i] = env.makeBitSet(numValues);
        }

        for (int i = 0; i < arity; ++i) {
            IntVar v = vars[i];
            DisposableValueIterator vit = v.getValueIterator(true);
            domIsRegular[i] = true;
            while (vit.hasNext()) {
                int val = vit.next();
                int valIdx = val2Idx.get(val);
                if (domIsRegular[i] && val != valIdx)
                    domIsRegular[i] = false;
                RB[valIdx].set(i);
                RD[i].set(valIdx);
            }
            vit.dispose();
        }

        // 记录访问过的变量
        visiting_ = new int[arity];
        unVisitedVariables = new SimpleBitSet(arity);
        // 变量的前驱变量，若前驱变量是-1，则表示无前驱变量，就是第一个变量
        variable_visited_from_ = new int[arity];
        visitedValues = new BitSet(numValues);
        matchedValuesR = env.makeBitSet(numValues);
        validValuesR = env.makeBitSet(numValues);
        A = new SimpleBitSet(numValues);
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

        gammaFrontier = new SimpleBitSet(arity);
        gammaMask = new SimpleBitSet(arity);

        graphLinkedMatrix = new SimpleBitSet[arity];
        graphLinkedFrontier = new SimpleBitSet[arity];
        for (int i = 0; i < arity; ++i) {
            graphLinkedMatrix[i] = new SimpleBitSet(arity);
            graphLinkedFrontier[i] = new SimpleBitSet(arity);
        }

        // for Gent algorithm
        partition = makePartition(arity, env);
        triggeringVars = new SparseSet(arity);
        // 已懒更新的变量/值
        varsTmp = new SparseSet(arity);
        changedSCCStartIndex = new SparseSet(arity);
        monitors = new IIntDeltaMonitor[vars.length];
        for (int i = 0; i < vars.length; i++) {
            monitors[i] = vars[i].monitorDelta(cause);
        }
        onValRem = makeProcedure();

        deletedValues = new SparseSet[arity];
        for (int i = 0; i < arity; i++) {
            deletedValues[i] = new SparseSet(numValues);
        }

        sccTriggeringVars = new TIntArrayList(arity);
    }

    protected UnaryIntProcedure<Integer> makeProcedure() {
        return new UnaryIntProcedure<Integer>() {
            int varIdx;
            IntVar v;
            int matchedVal = -1;

            @Override
            public UnaryIntProcedure set(Integer o) {
                varIdx = o;
                v = vars[varIdx];
                matchedVal = var2ValR[varIdx].get();
                return this;
            }

            @Override
            public void execute(int i) {
                int valIdx = domIsRegular[varIdx] ? i : val2Idx.get(i);
                // 删的值是匹配值，清理匹配
                if (valIdx == matchedVal) {
                    var2ValR[varIdx].set(-1);
                    val2VarR[valIdx].set(-1);
                    matchedValuesR.clear(valIdx);
                    freeNodesR.set(valIdx);
                }

                deletedValues[varIdx].add(valIdx);
                removeValueR(varIdx, valIdx);

                // bel删空表示该值失效
                if (RB[valIdx].isEmpty()) {
                    validValuesR.clear(valIdx);
                    freeNodesR.clear(valIdx);
                }

//                System.out.println("delta: " + varIdx + ", " + valIdx);
            }
        };
    }


    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    public boolean propagate() throws ContradictionException {
//        System.out.println(" propagate: " + (++numCall) + "----------------");
//        printDomains();
        boolean filter = false;
//        instVar.clear();
//        if (numCall == 24)
//            System.out.println(partition);
        changedVars.clear();
        Measurer.enterProp();
//        System.out.println(partition);
        if (initialPropagation) {
//            triggeringVals.fill();
//            triggeringVars.fill();
//            updatedVars.fill();
//            updatedVals.fill();
            startTime = System.nanoTime();
            deltaUpdate();
            findMaximumMatching();
            Measurer.matchingTime += System.nanoTime() - startTime;
//            System.out.println("matching: " + Arrays.toString(var2ValR));

            startTime = System.nanoTime();

//            A.setNegAnd(matchedValuesR, validValuesR);
//            System.out.println("freeNodes:\t" + A);
//            System.out.println("freeNodesR:\t" + freeNodesR);
//            if (!A.eq(freeNodesR)) {
//                System.out.println("free nodes error!!");
//            }
            // for Zhang18
            // 有freeNodes才执行。在gamma区中过滤
            A.set(freeNodesR);
            if (freeNodesR.isEmpty()) {
                initiateMatrixOrdinary(0);
                filter |= filterDomainsPartition(0);
            } else {
                int newSCCStart = distinguish();
//                System.out.println("gamma: " + gammaMask);
                if (newSCCStart != -1) {
                    filter |= filterDomainsGamma();
                    // gamma分裂区中建图过滤
                    initiateMatrixAfterGamma(newSCCStart);
//                    filter |= filterDomainsAfterGamma(newSCCStart);
                    filter |= filterDomainsPartition(newSCCStart);
                }
            }
            Measurer.filterTime += System.nanoTime() - startTime;
//            System.out.println(partition);
            initialPropagation = false;
        } else {
            startTime = System.nanoTime();
            deltaUpdate();
            filter |= propagate_SCC_Match();
//            System.out.println("matching: " + Arrays.toString(var2ValR));
            Measurer.matchingTime += System.nanoTime() - startTime;
            startTime = System.nanoTime();
            filter |= propagate_SCC_filter();
            Measurer.filterTime += System.nanoTime() - startTime;
        }
        dealChanges();
//        if (numCall == 683) {
//            printDomains();
//        }
//        System.out.println(partition);
        return filter;
    }

    //***********************************************************************************
    // Initialization
    //***********************************************************************************

    private void printDomains() {
        // 填充B和D
        for (int i = 0; i < arity; ++i) {
            IntVar v = vars[i];
            System.out.println(v);
        }
//
//        // 填充B和D
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            System.out.println(RD[i]);
//        }
    }

    private void deltaUpdate() throws ContradictionException {
        // 触发队列和更新队列
        triggeringVars.clear();
//        updatedVars.clear();
//        updatedVals.clear();

        for (int varIdx = 0; varIdx < arity; varIdx++) {
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
        }
    }

    private void MakeAugmentingPath(int start) {
        // Do a BFS and use visiting_ as a queue, with num_visited pointing
        // at its begin() and num_to_visit its end().
        // To switch to the augmenting path once a nonmatched value was found,
        // we remember the BFS tree in variable_visited_from_.

        // start传入的是变量
        // 执行一个BFS并使用visiting_作为一个队列，num_visited指向它的begin()，
        // num_to_visit指向它的end()。要在发现不匹配的值时切换到扩展路径，
        // 我们需要记住variable_visited_from_中的BFS树
        //
        int num_to_visit = 0;
        int num_visited = 0;
        // Enqueue start.
        // visit 里存的是变量
        visiting_[num_to_visit++] = start;
//        variable_visited_[start] = true;
//        variable_visited_.set(start);
        unVisitedVariables.clear(start);
        variable_visited_from_[start] = -1;

        while (num_visited < num_to_visit) {
            // Dequeue node to visit.
            int node = visiting_[num_visited++];
//            updateBitDom(node);
//            needVisitValues.setAfterAnd(D[node], unVisitedValues);
//            for (int valIdx = needVisitValues.firstSetBit(); valIdx != unVisitedValues.end(); valIdx = needVisitValues.nextSetBit(valIdx + 1)) {
            for (int valIdx = RD[node].nextSetBit(0); valIdx >= 0; valIdx = RD[node].nextSetBit(valIdx + 1)) {
                if (visitedValues.get(valIdx)) continue;
                visitedValues.set(valIdx);
//                updateBitBel(valIdx);
//                if (val2Var[valIdx] == -1) {
                if (!matchedValuesR.get(valIdx)) {
                    // value_to_variable_[valIdx] ， value这个值未分配到变量，即是一个free
                    // !! 这里可以改用bitSet 求原数据bitDom (successor_)
                    // 与matching的余集(matching_bitVector[a]，表示a是否已matching出去了) 再按1取未匹配值，
                    // 可以惰性取值，即先算两个集合的在特定位置的交：以matching_bv为长度foreach
                    // （一般不会特别长两个数据结构可以用NaiveBitSet，如400皇后，|D|=400，只需要7个，
                    // 做&后会得到一个或NaiveBitSet, LargeBitSet）
                    // valIdx is not matched: change path from node to start, and return.
                    // 未匹配值

                    // !! 路线回溯怎么用bit表示。
                    // !! 这里可以提前记一些scc或是路径
                    int path_node = node;
                    int path_value = valIdx;
                    while (path_node != -1) {
//                        // 旧变量拿到旧匹配值
//                        int old_value = var2Val[path_node];
//                        // 旧变量拿到新匹配值
//                        var2Val[path_node] = path_value;
//                        val2Var[path_value] = path_node;

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
//                    freeNode.remove(valIdx);
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

    // 第一次调用
    private void findMaximumMatching() throws ContradictionException {
//        // !! 可做增量
//        freeNode.fill();
        for (int varIdx = 0; varIdx < arity; varIdx++) {
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

    protected void repairMatching(int SCCStartIndex) throws ContradictionException {
        // repair max matching.
        partition.setIteratorIndexBySCCStartIndex(SCCStartIndex);
        while (partition.hasNext()) {
            int varIdx = partition.next();
//            updateBitDom(varIdx);
            int valIdx = var2ValR[varIdx].get();
            // 值失效
            if (valIdx == -1 || !RD[varIdx].get(valIdx)) {
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
        partition.disposeSCCIterator();
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

            // valIdx失效
            if (valIdx == -1 || !RD[xIdx].get(valIdx)) {
                repairMatching(sccStartIdx);
            }

            if (x.isInstantiated() && !partition.isSingletonByStartIndex(sccStartIdx)) {
                valIdx = var2ValR[xIdx].get();
                int xVal = idx2Val[valIdx];
                if (changedSCCStartIndex.contains(sccStartIdx)) {
                    changedSCCStartIndex.remove(sccStartIdx);
                }

                //parition s into s1 s2 , from now on s = s2
                partition.remove(xIdx);
//                System.out.println(partition);

                partition.setIteratorIndexBySCCStartIndex(sccStartIdx);
                while (partition.hasNext()) {
                    int yIdx = partition.next();
                    if (RD[yIdx].get(valIdx)) {
                        y = vars[yIdx];
//                        res |= y.removeValue(xVal, aCause);
//                        removeValue(yIdx, valIdx);
                        recordRemoveVal(yIdx, valIdx);
                        deletedValues[yIdx].add(valIdx);
                    }
                }
                partition.disposeSCCIterator();

                if (!partition.isSingletonByStartIndex(sccStartIdx)) {
                    changedSCCStartIndex.add(sccStartIdx);
                }

            } else {
                if (!partition.isSingletonByStartIndex(sccStartIdx)) {
                    changedSCCStartIndex.add(sccStartIdx);
                }
            }
        }
        return res;
    }

    protected boolean propagate_SCC_filter() throws ContradictionException {
        boolean filter = false;
        gammaMask.clear();
//        freeNodesR.generateBitSet(A);
        A.set(freeNodesR);
//        System.out.println("changed: " + changedSCCStartIndex);
//        System.out.println("freeNodes: " + freeNodesR);
//        System.out.println("gamma: " + gammaMask);
//        System.out.println("A: " + A);
//        System.out.println("trigger: " + triggeringVars);
        // for Zhang18
        // 带gamma的分区总在第0个分区中，
        // 若第0个分区changed并且freenode不为空。
        if (changedSCCStartIndex.contains(0) && !freeNodesR.isEmpty()) {
            // 有freeNodes才执行。在gamma区中过滤
            int newSCCStart = distinguish();
            // newSCCStart == -1 表示Gamma占据当前全部scc
            if (newSCCStart != INDEX_OVERFLOW) {
                filter |= filterDomainsGamma();

                // gamma分裂区中建图过滤
                initiateMatrixAfterGamma(newSCCStart);
                if (numSCCValues >= (numSCCDeleteValues << 1)) {
                    if (!earlyDetection()) {
                        Measurer.enterSkip();
                        filter |= filterDomainsPartition(newSCCStart);
                    }
                } else {
                    filter |= filterDomainsPartition(newSCCStart);
                }
//
//                filter |= filterDomainsAfterGamma(newSCCStart);

            }
            changedSCCStartIndex.remove(0);
        }

        changedSCCStartIndex.iterateValid();
        while (changedSCCStartIndex.hasNextValid()) {
            int sccStartIndex = changedSCCStartIndex.next();
            initiateMatrixOrdinary(sccStartIndex);
//            filter |= filterDomainsPartition(sccStartIndex);
            if (numSCCValues >= (numSCCDeleteValues << 1)) {
                if (!earlyDetection()) {
                    Measurer.enterSkip();
                    filter |= filterDomainsPartition(sccStartIndex);
                }
            } else {
                filter |= filterDomainsPartition(sccStartIndex);
            }
        }
        return filter;
    }

    //***********************************************************************************
    // PRUNING
    //***********************************************************************************
    // 只有changedSCCStartIndex包括索引0才会触发这个传播,反回除去gamma的新scc
    // 返回新SCCStartIndex，如果返回-1表示该SCC全部为gamma
    private int distinguish() {
//        notGamma.fill();
//        notA.fill();
        int numBit;
        gammaMask.clear();
//        freeNodesR.generateBitSet(A);
        A.set(freeNodesR);
//        // freeNode
//        if (!freeNodesR.isEmpty())
//            return ;
        int firstSCCSize = partition.getSCCSizeByStartIndex(0);
        for (int i = A.nextSetBit(0); i >= 0; i = A.nextSetBit(i + 1)) {
//            notA.remove(i);
            numBit = gammaMask.orCount(RB[i]);
            // 若notGamma为空，不需后续 直接退出
//            if (numCall == 2) {
//                System.out.println("add " + i + ": " + gammaMask);
//            }
            if (numBit == firstSCCSize)
                return INDEX_OVERFLOW;
        }

        gammaFrontier.set(gammaMask);


        for (int varIdx = gammaFrontier.nextSetBit(0);
             varIdx != -1; varIdx = gammaFrontier.nextSetBit(0)) {
            // !! 这里可以将Extended改成Frontier，只记录前沿，记录方法是三个BitSet比较，
            // frontier 扩展，从valMask中去掉gammaMask已记录的变量
            int valIdx = var2ValR[varIdx].get();
            gammaFrontier.orAfterMinus(RB[valIdx], gammaMask);
//            // 除去第i个变量
            gammaFrontier.clear(varIdx);
            // gamma 扩展
            numBit = gammaMask.orCount(RB[valIdx]);
            // 若notGamma为空，表示scc全部都在gamma，不需后续计算SCC，直接退出
            if (numBit == firstSCCSize)
                return INDEX_OVERFLOW;
            A.set(valIdx);
        }

        // 直接分裂SCCs,返回新SCC的StartIndex
//        int i = gammaMask.nextSetBit(0);
//        int sccStart = partition.getSCCStartIndexByElement(i);
        partition.setIteratorIndexBySCCStartIndex(0);
        for (int i = gammaMask.nextSetBit(0); i >= 0; i = gammaMask.nextSetBit(i + 1)) {
            partition.addGamma(i);
        }
        int newStart = partition.splitGamma();
        partition.disposeSCCIterator();
        return newStart;
    }

//    // 带Gamma的SCC才如下建模
//    private void initiateMatrixGamma() {
//        // 重置两个矩阵
//        // 不包括gamma子分区
//        partition.setIteratorIndexAfterGamma();
//        while (partition.hasNext()) {
//            int varIdx = partition.next();
////            updateBitDom(varIdx);
//            // 从变量id拿到匹配值再拿到该值所能到达的变量mask
//            int valIdx = var2ValR[varIdx].get();
////            updateBitBel(valIdx);
//            graphLinkedMatrix[varIdx].setAfterMinus(RB[valIdx], gammaMask);
//            graphLinkedMatrix[varIdx].clear(varIdx);
//            graphLinkedFrontier[varIdx].set(graphLinkedMatrix[varIdx]);
////            System.out.println("------graphLinkedMatrix[" + varIdx + "]------");
////            System.out.println(graphLinkedMatrix[varIdx]);
////            System.out.println(graphLinkedFrontier[varIdx]);
//        }
//
//        partition.disposeSCCIterator();
//    }


    // 分裂gamma后
    private void initiateMatrixAfterGamma(int sccStartIdx) {
        sccTriggeringVars.clear();
        numSCCDeleteValues = 0;
        numSCCValues = 0;
        // 重置两个矩阵
        // 只重置notGamma的变量
        partition.setIteratorIndexBySCCStartIndex(sccStartIdx);
        while (partition.hasNext()) {
            int varIdx = partition.next();
//            updateBitDom(varIdx);
            // 从变量id拿到匹配值再拿到该值所能到达的变量mask
            int valIdx = var2ValR[varIdx].get();
//            updateBitBel(valIdx);
            graphLinkedMatrix[varIdx].setAfterMinus(RB[valIdx], gammaMask);
            graphLinkedMatrix[varIdx].clear(varIdx);
            graphLinkedFrontier[varIdx].set(graphLinkedMatrix[varIdx]);

            // 初始化本scc的deletedVars
            if (triggeringVars.contains(varIdx)) {
                sccTriggeringVars.add(varIdx);
                numSCCDeleteValues += deletedValues[varIdx].validSize();
            }
            numSCCValues += vars[varIdx].getDomainSize();

//            System.out.println("------graphLinkedMatrix[" + varIdx + "]------");
//            System.out.println(graphLinkedMatrix[varIdx]);
//            System.out.println(graphLinkedFrontier[varIdx]);
        }
        partition.disposeSCCIterator();
    }

    private void initiateMatrixOrdinary(int sccStartIdx) {
        sccTriggeringVars.clear();
        numSCCDeleteValues = 0;
        numSCCValues = 0;
        // 重置两个矩阵
        // 只重置notGamma的变量
        partition.setIteratorIndexBySCCStartIndex(sccStartIdx);
        while (partition.hasNext()) {
            int varIdx = partition.next();
            // 从变量id拿到匹配值再拿到该值所能到达的变量mask
            int valIdx = var2ValR[varIdx].get();
            graphLinkedMatrix[varIdx].set(RB[valIdx]);
            graphLinkedMatrix[varIdx].clear(varIdx);
            graphLinkedFrontier[varIdx].set(graphLinkedMatrix[varIdx]);

            // 初始化本scc的deletedVars
            if (triggeringVars.contains(varIdx)) {
                sccTriggeringVars.add(varIdx);
                numSCCDeleteValues += deletedValues[varIdx].validSize();
            }
            numSCCValues += vars[varIdx].getDomainSize();
//            if (numCall == 106) {
//                System.out.println("------graphLinkedMatrix[" + varIdx + "]------");
//                System.out.println(graphLinkedMatrix[varIdx]);
//                System.out.println(graphLinkedFrontier[varIdx]);
//            }
        }
        partition.disposeSCCIterator();
    }

    /**
     * @return true if useless propagation
     */
    private boolean earlyDetection() {
        for (int i = 0, ub = sccTriggeringVars.size(); i < ub; i++) {
            int varIdx = sccTriggeringVars.get(i);
            SparseSet del = deletedValues[varIdx];
            del.iterateValid();
            while (del.hasNextValid()) {
                int valIdx = del.next();
                if (!validValuesR.get(valIdx)) {
                    return false;
                }
//                System.out.println("ED: check: " + varIdx + ", " + valIdx);
                if (!A.get(valIdx) && validValuesR.get(valIdx)) {
                    // 变量varIdx能到值valIdx且变量M(valIdx)能到M(varIdx)==>(varIdx,valIdx)是无效删值
                    if (!checkSCC(varIdx, valIdx) ||
                            !checkSCC(val2VarR[valIdx].get(), var2ValR[varIdx].get())) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    // 只用来过滤带有Gamma的SCC，全程不用算scc
    private boolean filterDomainsGamma() throws ContradictionException {
        boolean filter = false;
        partition.setIteratorIndexBySCCStartIndex(0);
        while (partition.hasNext()) {
            int varIdx = partition.next();
            // varIdx 只可能在两个子分区中，checked和unknown
            IntVar v = vars[varIdx];
            for (int valIdx = RD[varIdx].nextSetBit(0); valIdx >= 0; valIdx = RD[varIdx].nextSetBit(valIdx + 1)) {
                if (!A.get(valIdx)) {
                    // 变量在Gamma,值不在A
                    ++Measurer.numDelValuesP1;
                    Measurer.enterP1();
                    int k = idx2Val[valIdx];
//                    filter |= v.removeValue(k, aCause);
//                    removeValue(varIdx, valIdx);
                    recordRemoveVal(varIdx, valIdx);
//                    System.out.println("first delete1: " + varIdx + ", " + valIdx);
                }
            }
        }
        partition.disposeSCCIterator();
        return filter;
    }

    private boolean filterDomainsPartition(int sccStartIndex) throws ContradictionException {
        boolean filter = false;
        partition.setIteratorIndexBySCCStartIndex(sccStartIndex);
        while (partition.hasNext()) {
            // 分为三个分区：sccStart,checked,unknown,moved,sccEnd
            int varIdx = partition.nextAndSplitWhenMeetingUnknownAndMoved();
            // varIdx 只可能在两个子分区中，checked和unknown
            IntVar v = vars[varIdx];
            if (!v.isInstantiated()) {
                int matchedVal = var2ValR[varIdx].get();
                int k = idx2Val[matchedVal];
                // 先验证匹配值，再验证其它值
                if (!checkSCC(varIdx, matchedVal)) {
                    Measurer.enterP2();
                    int valNum = v.getDomainSize();
                    Measurer.numDelValuesP2 += valNum - 1;
//                    filter |= v.instantiateTo(k, aCause);
//                    filter |= instantiateTo(varIdx, matchedVal, v, k);
                    recordInstVar(varIdx, matchedVal);
                    partition.removeCurrentToTail();
//                    System.out.println("instantiate  : " + varIdx + ", " + matchedVal);
                    continue;
                } else {
                    // 匹配值在SCC中，表示变量论域至少两个值，且至少有一个值在SCC中
                    partition.setCurrentConnected();
                    // 再验证其它值
                    for (int valIdx = RD[varIdx].nextSetBit(0); valIdx >= 0; valIdx = RD[varIdx].nextSetBit(valIdx + 1)) {
                        // valIdx 可能在三个子分区内：connected，unknown和moved
                        // 在connected分区中不用验证，
                        // 在unknown分区中的需要检测scc
                        // 在moved分区中的直接移除

                        int varIdx2 = val2VarR[valIdx].get();
                        if (varIdx != varIdx2) {
                            k = idx2Val[valIdx];
                            if (partition.varInUnknown(varIdx2)) {
                                // 在Unknown分区中，需检查，能连通就加入Connected，不通连通就放入Moved分区
                                if (!checkSCC(varIdx, valIdx)) {
                                    Measurer.enterP2();
                                    ++Measurer.numDelValuesP2;
//                                    filter |= v.removeValue(k, aCause);
//                                    removeValue(varIdx, valIdx);
                                    recordRemoveVal(varIdx, valIdx);
//                                    if (partition.canMove(varIdx2)) {
                                    // varIdx2未分裂，将varIdx2移入tmp分区中
                                    partition.addMoved(varIdx2);
//                                    }
//                                    System.out.println("second delete1: " + varIdx + ", " + valIdx);
                                } else {
                                    partition.addConnected(varIdx2);
                                }
                            } else if (partition.varInMoved(varIdx2)) {
                                // var2在moved子分区,
                                Measurer.enterP2();
                                ++Measurer.numDelValuesP2;
//                                filter |= v.removeValue(k, aCause);
//                                removeValue(varIdx, valIdx);
                                recordRemoveVal(varIdx, valIdx);
//                                System.out.println("second delete2: " + varIdx + ", " + valIdx);

//                                if (partition.canMove(varIdx2)) {
//                                    // varIdx2未分裂，将varIdx2移入tmp分区中
//                                    partition.addMoved(varIdx2);
//                                }
                            } else if (partition.varNotInSameSCC(varIdx2)) {
                                // var2在moved子分区,
                                Measurer.enterP2();
                                ++Measurer.numDelValuesP2;
//                                filter |= v.removeValue(k, aCause);
//                                removeValue(varIdx, valIdx);
                                recordRemoveVal(varIdx, valIdx);
//                                System.out.println("second delete3: " + varIdx + ", " + valIdx);

                            }

                            // 如果在Connected分区或在其它SCC中，跳过该值

                        }
                    }
                }
            }
        }
        partition.disposeSCCIterator();
        return filter;
    }

    private boolean checkSCC(int x, int a) {
        int y = val2VarR[a].get();
        if (graphLinkedMatrix[x].get(y)) {
            return true;
        }
        for (int i = graphLinkedFrontier[x].nextSetBit(0);
             i >= 0; i = graphLinkedFrontier[x].nextSetBit(0)) {
            // frontier扩张，除掉变量i 因为变量i已被扩展。
            graphLinkedFrontier[x].orAfterMinus(graphLinkedMatrix[i], graphLinkedMatrix[x]);
            graphLinkedFrontier[x].clear(i);
            graphLinkedMatrix[x].or(graphLinkedMatrix[i]);
            if (graphLinkedMatrix[x].get(y)) {
                return true;
            }
        }
        return false;
    }

    @Override
    protected void removeValueR(int varIdx, int valIdx) {
        RD[varIdx].clear(valIdx);
        RB[valIdx].clear(varIdx);
    }

    @Override
    protected void instantiateToR(int varIdx, int valIdx) {
        RD[varIdx].clear();
        RD[varIdx].set(valIdx);
        RB[valIdx].clear();
        RB[valIdx].set(varIdx);
    }


//    // for lazy update, 最早在matching时，最晚在initiateMatrix时检测
//    void updateBitBel(int valIdx) {
//        // bit值未更新，此处更新
//        if (!updatedVals.contains(valIdx)) {
//            updatedVals.add(valIdx);
////            System.out.println("RB[" + valIdx + "]\t" + RB[valIdx]);
//            RB[valIdx].generateBitSet(B[valIdx]);
////            System.out.println("B[" + valIdx + "]\t" + B[valIdx]);
//        }
//    }
//
//    // for lazy update, 最早在matching时，最晚在initiateMatrix时检测
//    void updateBitDom(int varIdx) {
//        // bit值未更新，此处更新
//        if (!updatedVars.contains(varIdx)) {
//            updatedVars.add(varIdx);
////            System.out.println("RD[" + varIdx + "]\t" + RD[varIdx]);
//            RD[varIdx].generateBitSet(D[varIdx]);
////            System.out.println("D[" + varIdx + "]\t" + D[varIdx]);
//        }
//    }
}
