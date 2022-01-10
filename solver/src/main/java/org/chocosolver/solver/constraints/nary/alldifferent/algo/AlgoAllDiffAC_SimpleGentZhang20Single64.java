package org.chocosolver.solver.constraints.nary.alldifferent.algo;

//import org.chocosolver.amtf.Measurer;

import gnu.trove.list.array.TIntArrayList;
import org.chocosolver.memory.IStateBitSet;
import org.chocosolver.memory.IStateInt;
import org.chocosolver.memory.IStateLong;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
import org.chocosolver.util.iterators.DisposableValueIterator;
import org.chocosolver.util.objects.IStatePartition;
import org.chocosolver.util.objects.Measurer;
import org.chocosolver.util.objects.SimpleBitSet;
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
public class AlgoAllDiffAC_SimpleGentZhang20Single64 extends AlgoAllDiffAC_Simple {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************
    // 约束的个数
    static private int num = 0;
    static private long numCall = -1;
    static protected long lastMask;
    // 约束的编号
    // 新增一点（视为变量）
    // 自由值集合
    // 以下是bit版本所需数据结构========================
    // 已访问过的变量和值
    private long unVisitedVariables = 0;
    private long visitedValues = 0;
    private IStateLong matchedValuesR;
    // matching
    private IStateInt[] val2VarR;
    private IStateInt[] var2ValR;
    // 记录队列
    private int[] visiting_;
    private int[] variable_visited_from_;

    // 变量到变量的连通性
    // 对于惰性算法，记录是否知道-变量到变量的连通性
    private long[] graphLinkedMatrix;
    private long[] graphLinkedFrontier;

    // 记录scc
    protected boolean initialPropagation = true;
    protected IStatePartition partition;
    private SparseSet triggeringVars;
    //    private SparseSet triggeringVals;
    private IIntDeltaMonitor[] monitors;
    private UnaryIntProcedure<Integer> onValRem;
    private SparseSet[] deletedValues;
    //    protected SparseSet varsTmp;
    private SparseSet changedSCCStartIndex;
    // for early detect
    private TIntArrayList sccTriggeringVars;
    private int numSCCDeleteValues;
    private int numSCCValues;

    long startTime;
    //    // for backtrack
    IStateLong[] RB;
    IStateLong[] RD;
    // if all a in var x val2Idx[a] = a then DomIsRagular[x] = true
    boolean[] domIsRegular;


    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_SimpleGentZhang20Single64(IntVar[] variables, ICause cause, Model model) {
        super(variables, cause, model.getEnvironment());
        id = num++;
        lastMask = WORD_MASK >>> (BITS_PER_WORD - (arity % BITS_PER_WORD));
//        System.out.println("id: " + id + " Zhang20SingleBit");
        // System.out.println("-----------idx2Val-----------");
        // System.out.println(Arrays.toString(idx2Val));
        // for backtracking
        RB = new IStateLong[numValues];
        for (int i = 0; i < numValues; ++i) {
            RB[i] = env.makeLong(0);
        }

        RD = new IStateLong[arity];
        domIsRegular = new boolean[arity];
        for (int i = 0; i < arity; i++) {
            RD[i] = env.makeLong(0);
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
                set(RB[valIdx], i);
                set(RD[i], valIdx);
            }
            vit.dispose();
        }

        // 记录访问过的变量
        visiting_ = new int[arity];
//        unVisitedVariables = new SimpleBitSet(arity);
        // 变量的前驱变量，若前驱变量是-1，则表示无前驱变量，就是第一个变量
        variable_visited_from_ = new int[arity];
//        visitedValues = new BitSet(numValues);
//        matchedValues = new SimpleBitSet(numValues);
        matchedValuesR = env.makeLong();

        var2ValR = new IStateInt[arity];
        val2VarR = new IStateInt[numValues];

        for (int i = 0; i < arity; ++i) {
            var2ValR[i] = env.makeInt(-1);
        }
        for (int i = 0; i < numValues; ++i) {
            val2VarR[i] = env.makeInt(-1);
        }

//        freeNode = new SparseSet(numValues);
//        gammaFrontier = new SimpleBitSet(arity);
//        gammaMask = new SimpleBitSet(arity);
//        notGamma = new SparseSet(arity);
//        notA = new SparseSet(numValues);

        graphLinkedMatrix = new long[arity];
        graphLinkedFrontier = new long[arity];
//        for (int i = 0; i < arity; ++i) {
//            graphLinkedMatrix[i] = new SimpleBitSet(arity);
//            graphLinkedFrontier[i] = new SimpleBitSet(arity);
//        }

        // for Gent algorithm
        partition = makePartition(arity, env);
        triggeringVars = new SparseSet(arity);
//        triggeringVals = new SparseSet(numValues);
        // 已懒更新的变量/值
//        updatedVars = new SparseSet(arity);
//        updatedVals = new SparseSet(numValues);
//        varsTmp = new SparseSet(arity);
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
//                    matchedValuesR.clear(valIdx);
                    clear(matchedValuesR, valIdx);
                }

                deletedValues[varIdx].add(valIdx);
//                RB[valIdx].clear(varIdx);
//                RD[varIdx].clear(valIdx);
                removeValue(varIdx, valIdx);
//                System.out.println("delta: " + varIdx + ", " + valIdx);
            }
        };
    }


    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    public boolean propagate() throws ContradictionException {
//        System.out.println("----------------" + id + " propagate: " + (++numCall) + "----------------");
//        printDomains();
        boolean filter = false;
        Measurer.enterProp();
//        System.out.println(partition);
        if (initialPropagation) {
//            triggeringVals.fill();
            triggeringVars.fill();
//            updatedVars.fill();
//            updatedVals.fill();
            startTime = System.nanoTime();
            findMaximumMatching();
            Measurer.matchingTime += System.nanoTime() - startTime;
//            System.out.println("matching: " + Arrays.toString(var2ValR));
            startTime = System.nanoTime();
            initiateMatrix(0);
            filter = filterDomainsPartition(0);
            Measurer.filterTime += System.nanoTime() - startTime;
//            System.out.println(partition);
            initialPropagation = false;
        } else {
            deltaUpdate();
//            System.out.println("--------");
//            printDomains();
            startTime = System.nanoTime();
            filter |= propagate_SCC_Match();
//            if (numCall == 24)
//                System.out.println(partition);
//            System.out.println("matching: " + Arrays.toString(var2ValR));
            Measurer.matchingTime += System.nanoTime() - startTime;
            startTime = System.nanoTime();
            filter |= propagate_SCC_filter();
            Measurer.filterTime += System.nanoTime() - startTime;
        }
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
    }

    private void deltaUpdate() throws ContradictionException {
        // 触发队列和更新队列
        triggeringVars.clear();

        for (int varIdx = 0; varIdx < arity; varIdx++) {
            monitors[varIdx].freeze();
            int numDeltaSize = monitors[varIdx].sizeApproximation();
            if (numDeltaSize != 0) {
                // 变量发生改变
                deletedValues[varIdx].clear();
                triggeringVars.add(varIdx);
                // 只动变量论域改变的变量，触发变量和删值队列都更新一下
                monitors[varIdx].forEachRemVal(onValRem.set(varIdx));
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

//        System.out.println("------" + start + "------");
        int num_to_visit = 0;
        int num_visited = 0;
        // Enqueue start.
        // visit 里存的是变量
        visiting_[num_to_visit++] = start;
//        variable_visited_[start] = true;
//        variable_visited_.set(start);
//        unVisitedVariables.clear(start);
//        clear(unVisitedVariables, start);
        unVisitedVariables &= (~(1 << start));
        variable_visited_from_[start] = -1;

        while (num_visited < num_to_visit) {
            // Dequeue node to visit.
            int node = visiting_[num_visited++];
//            updateBitDom(node);
//            needVisitValues.setAfterAnd(D[node], unVisitedValues);
//            for (int valIdx = needVisitValues.firstSetBit(); valIdx != unVisitedValues.end(); valIdx = needVisitValues.nextSetBit(valIdx + 1)) {
//            System.out.println(Long.toBinaryString(RD[node].get()));
            for (int valIdx = nextSetBitNew(RD[node], 0); valIdx != BITS_PER_WORD;
                 valIdx = nextSetBitNew(RD[node], valIdx + 1)) {
//                System.out.println(Long.toBinaryString(visitedValues));
                if (get(visitedValues, valIdx)) continue;
//                System.out.println("out:" + node + "," + valIdx);
//                set(visitedValues, valIdx);
                visitedValues |= (1 << valIdx);
//                updateBitBel(valIdx);
//                if (val2Var[valIdx] == -1) {
                if (!get(matchedValuesR, valIdx)) {
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

//                    freeNode.clear(valIdx);
//                    freeNode.remove(valIdx);
                    set(matchedValuesR, valIdx);
//                    System.out.println(valIdx + " is not free");
                    return;
                } else {
                    // Enqueue node matched to valIdx.
                    // 若没有该值已经有匹配，但变量没有匹配

                    // 先拿到这个值的匹配变量
//                    int next_node = val2Var[valIdx];
                    int next_node = val2VarR[valIdx].get();
//                    System.out.println("nextNode: " + next_node);
//                    variable_visited_.set(next_node);
//                    clear(unVisitedVariables, next_node);
                    unVisitedVariables &= (~(1 << next_node));
//                    clear(unVisitedVariables, );
//                    System.out.println(num_to_visit + "," + next_node);
                    // 把这个变量加入队列中
                    visiting_[num_to_visit++] = next_node;
                    variable_visited_from_[next_node] = node;
//                    freeNode.clear(valIdx);
//                    freeNode.remove(valIdx);
                    set(matchedValuesR, valIdx);
                }
            }
        }
    }

    private void findMaximumMatching() throws ContradictionException {
//        // !! 可做增量
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            if (var2ValR[varIdx].get() == -1) {
//                clear(visitedValues);
                visitedValues = 0;
//                set(unVisitedVariables);
                unVisitedVariables = lastMask;
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
            int valIdx = var2ValR[varIdx].get();
            // 值失效
            if (valIdx == -1 || !get(RD[varIdx], valIdx)) {
                var2ValR[varIdx].set(-1);
//                clear(visitedValues);
                visitedValues = 0;
//                set(unVisitedVariables);
                unVisitedVariables = lastMask;
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
//        System.out.println(partition);
        triggeringVars.iterateValid();
        while (triggeringVars.hasNextValid()) {
            int xIdx = triggeringVars.next();
//            updateBitDom(xIdx);
            int valIdx = var2ValR[xIdx].get();

            int sccStartIdx = partition.getSCCStartIndexByElement(xIdx);
            x = vars[xIdx];

            // valIdx失效
            if (valIdx == -1 || !get(RD[xIdx], valIdx)) {
                repairMatching(sccStartIdx);
            }

            if (x.isInstantiated() && !partition.isSingletonByStartIndex(sccStartIdx)) {
                valIdx = var2ValR[xIdx].get();
//                updateBitBel(valIdx);
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
//                    updateBitDom(yIdx);
                    if (get(RD[yIdx], valIdx)) {
                        y = vars[yIdx];
                        res |= y.removeValue(xVal, aCause);
                        removeValue(yIdx, valIdx);
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
        changedSCCStartIndex.iterateValid();
        while (changedSCCStartIndex.hasNextValid()) {
            int sccStartIndex = changedSCCStartIndex.next();
            initiateMatrix(sccStartIndex);

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

    private void initiateMatrix(int sccStartIdx) {
        // 重置两个矩阵
        // 只重置notGamma的变量
        sccTriggeringVars.clear();
        numSCCDeleteValues = 0;
        numSCCValues = 0;

        partition.setIteratorIndexBySCCStartIndex(sccStartIdx);
        while (partition.hasNext()) {
            int varIdx = partition.next();
            // 从变量id拿到匹配值再拿到该值所能到达的变量mask
            int valIdx = var2ValR[varIdx].get();
            // graphLinkedMatrix[varIdx].set(RB[valIdx]);
            graphLinkedMatrix[varIdx] = RB[valIdx].get();
            // graphLinkedMatrix[varIdx].clear(varIdx);
            graphLinkedMatrix[varIdx] &= (~(1 << varIdx));
            // graphLinkedFrontier[varIdx].set(graphLinkedMatrix[varIdx]);
            graphLinkedFrontier[varIdx] = graphLinkedMatrix[varIdx];

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

    }

    private boolean filterDomains(int sccStartIndex) throws ContradictionException {
        boolean filter = false;
        partition.setIteratorIndexBySCCStartIndex(sccStartIndex);
        while (partition.hasNext()) {
            int varIdx = partition.nextAndSplitWhenMeetingUnknownAndMoved();
            IntVar v = vars[varIdx];
            if (!v.isInstantiated()) {

                int matchedVal = var2ValR[varIdx].get();
                int k = idx2Val[matchedVal];
                // 先验证匹配值，再验证其它值
                if (!checkSCC(varIdx, matchedVal)) {
                    int valNum = v.getDomainSize();
                    Measurer.numDelValuesP2 += valNum - 1;
                    filter |= v.instantiateTo(k, aCause);
                    instantiateTo(varIdx, matchedVal);
                    partition.removeCurrentToTail();
                    continue;
                    // System.out.println("instantiate  : " + v.getName() + ", " + k);
                } else {
                    partition.setCurrentConnected();
                    // 再验证其它值
//                    for (int valIdx = RD[varIdx].nextSetBit(0); valIdx >= 0; valIdx = RD[varIdx].nextSetBit(valIdx + 1)) {
                    for (int valIdx = nextSetBit(RD[varIdx], 0); valIdx >= 0;
                         valIdx = nextSetBit(RD[varIdx], valIdx + 1)) {
                        int varIdx2 = val2VarR[valIdx].get();
                        if (valIdx != varIdx2) {
                            k = idx2Val[valIdx];
                            if (!checkSCC(varIdx, varIdx2)) {
                                Measurer.enterP2();
                                ++Measurer.numDelValuesP2;
                                filter |= v.removeValue(k, aCause);
                                removeValue(varIdx, valIdx);
                                if (partition.canMove(varIdx2)) {
                                    // varIdx2未分裂，将varIdx2移入tmp分区中
                                    partition.addMoved(varIdx2);
                                }
                                // System.out.println("second delete: " + v.getName() + ", " + k);
                            } else {
                                partition.addConnected(varIdx2);
                            }
                        }
                    }
                }
            }
        }
        partition.disposeSCCIterator();
        return filter;
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
                // 变量varIdx能到值valIdx且变量M(valIdx)能到M(varIdx)==>(varIdx,valIdx)是无效删值
                if (!checkSCC(varIdx, valIdx) ||
                        !checkSCC(val2VarR[valIdx].get(), var2ValR[varIdx].get())) {
                    return false;
                }
            }
        }
        return true;
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
                    filter |= v.instantiateTo(k, aCause);
                    instantiateTo(varIdx, matchedVal);
                    partition.removeCurrentToTail();
//                    System.out.println("instantiate  : " + varIdx + ", " + matchedVal);
                    continue;
                } else {
                    // 匹配值在SCC中，表示变量论域至少两个值，且至少有一个值在SCC中
                    partition.setCurrentConnected();
                    // 再验证其它值
//                    for (int valIdx = RD[varIdx].nextSetBit(0); valIdx >= 0; valIdx = RD[varIdx].nextSetBit(valIdx + 1)) {
                    for (int valIdx = nextSetBit(RD[varIdx], 0); valIdx >= 0;
                         valIdx = nextSetBit(RD[varIdx], valIdx + 1)) {
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
                                    filter |= v.removeValue(k, aCause);
                                    removeValue(varIdx, valIdx);
                                    // varIdx2未分裂，将varIdx2移入tmp分区中
                                    partition.addMoved(varIdx2);
//                                    System.out.println("second delete1: " + varIdx + ", " + valIdx);
                                } else {
                                    partition.addConnected(varIdx2);
                                }
                            } else if (partition.varInMoved(varIdx2)) {
                                // var2在moved子分区,
                                Measurer.enterP2();
                                ++Measurer.numDelValuesP2;
                                filter |= v.removeValue(k, aCause);
                                removeValue(varIdx, valIdx);
//                                System.out.println("second delete2: " + varIdx + ", " + valIdx);
                                // varIdx2未分裂，将varIdx2移入tmp分区中
                            } else if (partition.varNotInSameSCC(varIdx2)) {
                                // var2在moved子分区,
                                Measurer.enterP2();
                                ++Measurer.numDelValuesP2;
                                filter |= v.removeValue(k, aCause);
//                                System.out.println("second delete3: " + varIdx + ", " + valIdx);
                                removeValue(varIdx, valIdx);
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
//        if (graphLinkedMatrix[x].get(y)) {
        if (get(graphLinkedMatrix[x], y)) {
            return true;
        }
//        for (int i = graphLinkedFrontier[x].nextSetBit(0); i >= 0; i = graphLinkedFrontier[x].nextSetBit(0)) {
        for (int i = nextSetBitNew(graphLinkedFrontier[x], 0); i != BITS_PER_WORD;
             i = nextSetBitNew(graphLinkedFrontier[x], 0)) {
            // frontier扩张，除掉变量i 因为变量i已被扩展。
//            graphLinkedFrontier[x].orAfterMinus(graphLinkedMatrix[i], graphLinkedMatrix[x]);
//            graphLinkedFrontier[x].clear(i);
//            graphLinkedMatrix[x].or(graphLinkedMatrix[i]);

            graphLinkedFrontier[x] |= graphLinkedMatrix[i] & ~graphLinkedMatrix[x];
//            clear(graphLinkedFrontier[x], i);
            graphLinkedFrontier[x] &= (~(1 << i));
            graphLinkedMatrix[x] |= graphLinkedMatrix[i];
            if (get(graphLinkedMatrix[x], y)) {
                return true;
            }
        }
        return false;
    }

    void removeValue(int varIdx, int valIdx) {
//        RD[varIdx].clear(valIdx);
//        RB[valIdx].clear(varIdx);

        clear(RD[varIdx], valIdx);
        clear(RB[valIdx], varIdx);
    }

    void instantiateTo(int varIdx, int valIdx) {
//        RD[varIdx].clear();
//        RD[varIdx].set(valIdx);
//        RB[valIdx].clear();
//        RB[valIdx].set(varIdx);

        clear(RD[varIdx]);
        set(RD[varIdx], valIdx);
        clear(RB[valIdx]);
        set(RB[valIdx], varIdx);
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
