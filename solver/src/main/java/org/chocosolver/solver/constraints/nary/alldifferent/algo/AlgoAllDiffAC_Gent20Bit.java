package org.chocosolver.solver.constraints.nary.alldifferent.algo;

//import org.chocosolver.amtf.Measurer;

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.iterator.TIntIterator;
import gnu.trove.list.array.TIntArrayList;
import gnu.trove.map.hash.TIntIntHashMap;
import gnu.trove.set.hash.TIntHashSet;
import gnu.trove.stack.array.TLongArrayStack;
import org.chocosolver.memory.IEnvironment;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
import org.chocosolver.util.objects.*;
import org.chocosolver.util.procedure.UnaryIntProcedure;

import java.util.Arrays;

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
public class AlgoAllDiffAC_Gent20Bit {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************
    // 约束的个数
    static public int num = 0;

    // 约束的编号
    private int id;
    protected long numCall = -1;

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

    private int numNode;
    // 值到索引
    private int[] idx2Val;
    // 索引到值
    private TIntIntHashMap val2Idx;

    // 与值相连的变量
    private INaiveBitSet[] B;
    private INaiveBitSet[] D;

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
    private int nbSCC;
    private int[] varSCC;
    private int[] valSCC;

    private int maxDFS = 1;
    private int[] varDFSNum;
    private int[] valDFSNum;
    private int[] varLowLink;
    private int[] valLowLink;
    private boolean hasSCCSplit = false;
    private int sccSize = 0;

    int sinkDFSNum;
    int sinkLowLink;
    boolean sinkIsInStack;

    private INaiveBitSet singleton;
    private INaiveBitSet restriction;
    private boolean sinkIsUnvisited;
    private boolean initialProp = true;
    private int endBitIndex = 64;

    private SparseSet triggeringVars;
    private TIntHashSet SCCStartIndex;
    private TIntHashSet changedSCCStartIndex;
    private RSetPartition partition;
    private TLongArrayStack DE;
    private static int INT_SIZE = 32;
    private BitIntervalSet cycles;
    private TIntArrayList[] deletedValues;


    // for delta update
    protected IIntDeltaMonitor[] monitors;
    private UnaryIntProcedure<Integer> onValRem;

    private boolean unconnected;
    private IntTuple2 nodePair;


    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_Gent20Bit(IntVar[] variables, ICause cause, Model model) {
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
        idx2Val = new int[numValues];
        TIntIntIterator it = val2Idx.iterator();
        while (it.hasNext()) {
            it.advance();
            idx2Val[it.value()] = it.key();
        }

        numNode = addArity + numValues;
//        System.out.println("-----------idx2Val-----------");
//        System.out.println(Arrays.toString(idx2Val));

        B = new INaiveBitSet[numValues];
        for (int i = 0; i < numValues; ++i) {
            B[i] = INaiveBitSet.makeBitSet(arity, false);
        }

        D = new INaiveBitSet[arity];
        for (int i = 0; i < arity; ++i) {
            D[i] = INaiveBitSet.makeBitSet(numValues, false);
        }

        // 填充B和D
        for (int i = 0; i < arity; ++i) {
            v = vars[i];
            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
                int valIdx = val2Idx.get(j);
                D[i].set(valIdx);
                B[valIdx].set(i);
            }
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
        singleton = INaiveBitSet.makeBitSet(arity, false);
        restriction = INaiveBitSet.makeBitSet(numNode, true);
//        varTmpMask = INaiveBitSet.makeBitSet(arity, false);

        // for bit DFS
        varStack = new int[arity];
        valStack = new int[numValues];

        varIsInStack = INaiveBitSet.makeBitSet(arity, false);
        valIsInStack = INaiveBitSet.makeBitSet(numValues, false);

        varSCC = new int[arity];
        valSCC = new int[numValues];

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

        triggeringVars = new SparseSet(arity);
        SCCStartIndex = new TIntHashSet();
        changedSCCStartIndex = new TIntHashSet();
        DE = new TLongArrayStack();
        deletedValues = new TIntArrayList[arity];
        for (int i = 0; i < arity; i++) {
            deletedValues[i] = new TIntArrayList(numValues);
        }
        partition = new RSetPartition(addArity + numValues, env);
        cycles = new BitIntervalSet(addArity + numValues + 2);

        // for delta
        monitors = new IIntDeltaMonitor[vars.length];
        for (int i = 0; i < vars.length; i++) {
            monitors[i] = vars[i].monitorDelta(cause);
        }
        onValRem = makeProcedure();

        nodePair = new IntTuple2(-1, -1);
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
            public void execute(int i) throws ContradictionException {
//                DE.push(getIntTuple2Long(var, val2Idx.get(i) + addArity));
                if (!triggeringVars.contains(var)) {
                    triggeringVars.add(var);
                    deletedValues[var].clear();
                }

                deletedValues[var].add(val2Idx.get(i));
            }
        };
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    public boolean propagate() throws ContradictionException {
//        System.out.println("---------------");
//        System.out.println("propagate cid: " + id);
        numCall++;
//        if (numCall<20) {
        System.out.println("----------------" + id + " propagate: " + numCall + "----------------");
//            printDoms();
//        }
        Measurer.enterProp();
        boolean filter = false;
        startTime = System.nanoTime();
        fillBandD();
        triggeringVars.clear();

        if (initialProp) {
            for (int i = 0; i < arity; i++) {
                triggeringVars.add(i);
            }
            initialProp = false;
            prepareForMatching();
            findMaximumMatching();
            Measurer.matchingTime += System.nanoTime() - startTime;

            startTime = System.nanoTime();
            filter = filter();
        } else {
//            DE.clear();
//            triggeringVars.clear();
            for (int i = 0; i < arity; ++i) {
                monitors[i].freeze();
                monitors[i].forEachRemVal(onValRem.set(i));
            }
//            System.out.println("triggeringVars: " + triggeringVars);
//            System.out.println("triggeringVars: " + DE);
//            getAllSCCStartIndices(SCCStartIndex);
//            System.out.println("triggeringVars: " + triggeringVars);
//            System.out.println(partition);
            prepareForMatching();
            filter |= propagate_SCC_Match();
            Measurer.matchingTime += System.nanoTime() - startTime;
//            System.out.println("SCCStartIndex: " + changedSCCStartIndex);

            startTime = System.nanoTime();
            filter |= propagate_SCC_filter();
            for (int i = 0; i < vars.length; i++) {
                monitors[i].unfreeze();
            }
        }

        Measurer.filterTime += System.nanoTime() - startTime;
        return filter;
    }

    //***********************************************************************************
    // Initialization
    //***********************************************************************************

    private void printDomains() {
        System.out.println("-----print domain-------");
        for (int i = 0; i < numValues; ++i) {
            System.out.println("val " + "i: " + B[i]);
        }

        IntVar v;
        // 填充B和D
        for (int i = 0; i < arity; ++i) {
            v = vars[i];
            System.out.println("val " + "i: " + D[i]);
            System.out.println(v);
        }
    }

    private void fillBandD() {
        for (int i = 0; i < numValues; ++i) {
            B[i].clear();
        }

        IntVar v;
        // 填充B和D
        for (int i = 0; i < arity; ++i) {
            D[i].clear();
            v = vars[i];
            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
                int valIdx = val2Idx.get(j);
                D[i].set(valIdx);
                B[valIdx].set(i);
            }
        }
    }

    private void prepareForMatching() {
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
            if (D[varIdx].isSingleton()) {
                // 取出变量的唯一值
                int valIdx = D[varIdx].firstSetBit();
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
//                    if (!v.contains(idx2Val[oldMatchingIndex])) {
                    if (!D[varIdx].get(oldMatchingIndex)) {
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

//                for (int value = v.getLB(), ub = v.getUB(); value <= ub; value = v.nextValue(value)) {
//                    int valIdx = val2Idx.get(value);
//                    // Forward-checking should propagate xsu != value.
//                    // !! 可以增量修改值
////                    B[valIdx].set(varIdx);
//                }
            }
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

            needVisitValues.setAfterAnd(D[node], unVisitedValues);
            for (int valIdx = needVisitValues.firstSetBit(); valIdx != unVisitedValues.end(); valIdx = needVisitValues.nextSetBit(valIdx + 1)) {
                if (!unVisitedValues.get(valIdx)) continue;
                unVisitedValues.clear(valIdx);
//                if (val2Var[valIdx] == -1) {
                if (!matchedValues.get(valIdx)) {
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
////--------------------------------------

        }
    }

    private void findMaximumMatching() throws ContradictionException {
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
    }

    private void repairMatching(int SCCStartIndex) throws ContradictionException {
        // Compute max matching.
        partition.setIteratorIndex(SCCStartIndex);
//        for (int varIdx = 0; varIdx < arity; varIdx++) {
        do {
            int varIdx = partition.getValue();
            if (varIdx < arity) {
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
        } while (partition.nextValid());
    }

    //***********************************************************************************
    // Independent SCCs
    //***********************************************************************************


    private boolean propagate_SCC_Match() throws ContradictionException {
//        StringBuilder sb = new StringBuilder();
//        sb.append("-------\n");
//        sb.append("propagate_SCC_Match\ntriggerVar: ");
//        triggeringVars.iterateValid();
//        while (triggeringVars.hasNextValid()) {
//            sb.append(triggeringVars.next()).append(" ");
//        }
//        sb.append("\n");
//        sb.append("-------\n");
//        System.out.println(sb.toString());

        boolean res = false;
        IntVar x, y;
//        changedSCCs.clear();
        changedSCCStartIndex.clear();
        triggeringVars.iterateValid();
//        TIntArrayList s;
//        TIntIterator iter;
        while (triggeringVars.hasNextValid()) {
            int xIdx = triggeringVars.next();
            int valIdx = var2Val[xIdx];
            int sccStartIdx = partition.getSCCStartIndexByElement(xIdx);
            x = vars[xIdx];

            if (valIdx == -1) {
                repairMatching(sccStartIdx);
            }

            if (x.isInstantiated() && partition.greatThanOne(sccStartIdx)) {
                int xVal = vars[xIdx].getValue();

                if (changedSCCStartIndex.contains(sccStartIdx)) {
                    changedSCCStartIndex.remove(sccStartIdx);
                }

                //parition s into s1 s2 , from now on s = s2
                partition.remove(xIdx);
                partition.setIteratorIndex(sccStartIdx);
                do {
                    int yIdx = partition.getValue();
                    if (yIdx < arity) {
                        y = vars[yIdx];
                        if (y.contains(xVal)) {
                            res |= y.removeValue(xVal, aCause);
                            System.out.println("remove: " + yIdx + "," + xVal);
                            int xValIdx = val2Idx.get(xVal);
                            D[yIdx].clear(xValIdx);
                            B[xValIdx].clear(yIdx);
                        }
                    }
                } while (partition.nextValid());

                if (partition.greatThanOne(sccStartIdx)) {
                    changedSCCStartIndex.add(sccStartIdx);
                }

            } else {
                if (partition.greatThanOne(sccStartIdx)) {
                    changedSCCStartIndex.add(sccStartIdx);
                }
            }
        }

        return res;
    }

    //生成DE
    private boolean propagate_SCC_filter() throws ContradictionException {
//        buildGraph();
////        SCCfinder.setUnvisitedValues();
//        SCCfinder.resetData();
        resetData();
        boolean isSkip = true;
        var iter = changedSCCStartIndex.iterator();
        while (iter.hasNext()) {
            DE.clear();
            cycles.clear();
            int sccStartIndex = iter.next();
            partition.setIteratorIndex(sccStartIndex);
            do {
                int varIdx = partition.getValue();
//                System.out.println("varIdx: " + varIdx + ", " + (varIdx < arity && triggeringVars.contain(varIdx)));
                if (varIdx < arity && triggeringVars.contains(varIdx)) {
                    var valIter = deletedValues[varIdx].iterator();
                    while ((valIter.hasNext())) {
                        DE.push(getIntTuple2Long(varIdx, valIter.next()));
                    }
                }
            } while (partition.nextValid());

//            var deArr = DE.toArray();
//            System.out.print("de: ");
//            for (var a : deArr) {
//                System.out.print(getIntTuple2(a) + " ");
//            }
//            System.out.println();

//            System.out.println("startIndex: " + startIdx);
            System.out.println("valDFSNum: " + Arrays.toString(valDFSNum)+", "+restriction+","+partition);
            boolean res = findAllSCC(sccStartIndex);
            isSkip = res && isSkip;
        }

//        System.out.println(Arrays.toString(varSCC));
//        System.out.println(Arrays.toString(valSCC));
//        System.out.println(partition);

        // isSkip全是true才ED有不是true的表明删值了
        if (isSkip) {
            Measurer.enterSkip();
            return true;
        }

        boolean filter = filterDomains();
        return filter;
    }


    //***********************************************************************************
    // PRUNING
    //***********************************************************************************
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
//             varIdx != gammaFrontier.end(); varIdx = gammaFrontier.nextSetBit(0)) {
//            // !! 这里可以将Extended改成Frontier，只记录前沿，记录方法是三个BitSet比较，
//            // frontier 扩展，从valMask中去掉gammaMask已记录的变量
//            int valIdx = var2Val[varIdx];
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
//                graphLinkedMatrix[varIdx].setAfterMinus(B[var2Val[varIdx]], gammaMask);
//                graphLinkedMatrix[varIdx].clear(varIdx);
//                graphLinkedFrontier[varIdx].set(graphLinkedMatrix[varIdx]);
//            }
////                System.out.println("------graphLinkedMatrix[" + varIdx + "]------");
////                System.out.println(graphLinkedMatrix[varIdx]);
////                System.out.println(graphLinkedFrontier[varIdx]);
//        }
//    }
//
//    private boolean filter() throws ContradictionException {
//        distinguish();
//        initiateMatrix();
//        // 这里判断一下，如果notGamma为空则不用进行如下步骤
//        boolean filter = false;
//        for (int varIdx = 0; varIdx < arity; varIdx++) {
//            IntVar v = vars[varIdx];
//            if (!v.isInstantiated()) {
////                int ub = v.getUB();
////                for (int k = v.getLB(); k <= ub; k = v.nextValue(k)) {
////                    int valIdx = val2Idx.get(k);
//                for (int valIdx = D[varIdx].firstSetBit(); valIdx != D[varIdx].end(); valIdx = D[varIdx].nextSetBit(valIdx + 1)) {
//                    int k = idx2Val[valIdx];
////                    System.out.println(valIdx);
//                    if (!notGamma.contain(varIdx) && notA.contain(valIdx)) {
//                        ++Measurer.numDelValuesP1;
//                        Measurer.enterP1();
//                        D[varIdx].clear(valIdx);
//                        filter |= v.removeValue(k, aCause);
//                        //                System.out.println("first delete: " + v.getName() + ", " + k);
//                    } else if (notGamma.contain(varIdx) && notA.contain(valIdx)) {
//                        if (!graphLinkedMatrix[varIdx].get(val2Var[valIdx]) && !checkSCC(varIdx, valIdx)) {
//                            Measurer.enterP2();
//                            if (valIdx == var2Val[varIdx]) {
//                                int valNum = v.getDomainSize();
//                                Measurer.numDelValuesP2 += valNum - 1;
//                                D[varIdx].clear();
//                                D[varIdx].set(valIdx);
//                                filter |= v.instantiateTo(k, aCause);
////                            System.out.println("instantiate  : " + v.getName() + ", " + k);
//                            } else {
//                                ++Measurer.numDelValuesP2;
//                                D[varIdx].clear(valIdx);
//                                filter |= v.removeValue(k, aCause);
////                            System.out.println("second delete: " + v.getName() + ", " + k);
//                            }
//                        }
//                    }
//                }
//            }
//        }
//        return filter;
//    }
//
//    private boolean checkSCC(int varIdx, int valIdx) {
////        System.out.println("check:" + varIdx + ", " + valIdx);
//        // 若没有 就需要BFS一下Frontier没有，就表示不用扩展了
//        // 注意一下return退出时frontier正确
//        for (int i = graphLinkedFrontier[varIdx].nextSetBit(0);
//             i != graphLinkedFrontier[varIdx].end(); i = graphLinkedFrontier[varIdx].nextSetBit(0)) {
//            // frontier扩张，除掉变量i 因为变量i已被扩展。
//            graphLinkedFrontier[varIdx].orAfterMinus(graphLinkedMatrix[i], graphLinkedMatrix[varIdx]);
//            graphLinkedFrontier[varIdx].clear(i);
//            graphLinkedMatrix[varIdx].or(graphLinkedMatrix[i]);
//            if (graphLinkedMatrix[varIdx].get(val2Var[valIdx])) {
//                return true;
//            }
//        }
//        return false;
//    }

    private boolean filterDomains() throws ContradictionException {
        boolean filter = false;

        for (int varIdx = 0; varIdx < arity; varIdx++) {
            IntVar v = vars[varIdx];
            if (!v.isInstantiated()) {
                for (int valIdx = D[varIdx].firstSetBit(); valIdx != D[varIdx].end(); valIdx = D[varIdx].nextSetBit(valIdx + 1)) {
                    int k = idx2Val[valIdx];
                    if (varSCC[varIdx] != valSCC[valIdx]) {
                        Measurer.enterP2();
                        if (valIdx == var2Val[varIdx]) {
                            int valNum = v.getDomainSize();
                            Measurer.numDelValuesP2 += valNum - 1;
//                            System.out.println("instantiate  : " + v.getName() + ", " + k + " P2: " + Measurer.numDelValuesP2);
                            filter |= v.instantiateTo(k, aCause);
                        } else {
                            ++Measurer.numDelValuesP2;
//                            System.out.println("second delete: " + v.getName() + ", " + k + " P2: " + Measurer.numDelValuesP2);
                            filter |= v.removeValue(k, aCause);
                        }
                    }
                }
            }
        }
        return filter;
    }

    private boolean filter() throws ContradictionException {
        boolean filter = false;

        resetData();

//        findAllSCC();
        partition.getSCCStartIndex(SCCStartIndex);
        TIntIterator iter = SCCStartIndex.iterator();
        while (iter.hasNext()) {
            findAllSCC(iter.next());
        }

//        System.out.println(Arrays.toString(varSCC));
//        System.out.println(Arrays.toString(valSCC));
//        System.out.println(partition);
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            IntVar v = vars[varIdx];
            if (!v.isInstantiated()) {
                for (int valIdx = D[varIdx].firstSetBit(); valIdx != D[varIdx].end(); valIdx = D[varIdx].nextSetBit(valIdx + 1)) {
                    int k = idx2Val[valIdx];
                    if (varSCC[varIdx] != valSCC[valIdx]) {
                        Measurer.enterP2();
                        if (valIdx == var2Val[varIdx]) {
                            int valNum = v.getDomainSize();
                            Measurer.numDelValuesP2 += valNum - 1;
//                            System.out.println("instantiate  : " + v.getName() + ", " + k + " P2: " + Measurer.numDelValuesP2);
                            filter |= v.instantiateTo(k, aCause);
                        } else {
                            ++Measurer.numDelValuesP2;
//                            System.out.println("second delete: " + v.getName() + ", " + k + " P2: " + Measurer.numDelValuesP2);
                            filter |= v.removeValue(k, aCause);
                        }
                    }
                }
            }
        }
        return filter;
    }

    private void resetData() {
        maxDFS = 0;
        nbSCC = 0;
//        unconnected = false;
//        cycles.clear();

        for (int i = 0; i < arity; i++) {
            varLowLink[i] = Integer.MAX_VALUE;
            varSCC[i] = -1;
            varDFSNum[i] = Integer.MAX_VALUE;
        }

        for (int i = 0; i < numValues; i++) {
            valLowLink[i] = Integer.MAX_VALUE;
            valSCC[i] = -1;
            valDFSNum[i] = Integer.MAX_VALUE;
        }

        sinkDFSNum = Integer.MAX_VALUE;
        sinkLowLink = Integer.MAX_VALUE;
        sinkIsInStack = false;
        sinkIsUnvisited = true;

        unVisitedVariables.set();
        unVisitedValues.set();
        singleton.clear();
    }

    // for initial propagate
    private void findAllSCC() {
        // initialization
        restriction.clear();
        restriction.set();

//        resetData();

        clearVarStack();
        clearValStack();

        findSingletons();
//        singleton.flip();
//        System.out.println("----------");
//        System.out.println("singleton:" + singleton);
//        System.out.println("restriction: " + restriction);
//        System.out.println("partition: " + partition);
        for (int varIdx = restriction.firstSetBit(); varIdx < arity; varIdx = restriction.nextSetBit(varIdx + 1)) {
//            if (unVisitedVariables.get(varIdx)) {
//                System.out.println(varIdx);
//            System.out.printf("out: %d\n", varIdx);
            strongConnectVar(varIdx);
//            }
        }

//        System.out.println(Arrays.toString(varSCC));
//        System.out.println(Arrays.toString(valSCC));
    }

    private boolean findAllSCC(int sccStartIdx) {
        // initialization
//        resetData();
        restriction.clear();
        cycles.clear();

        unconnected = false;
        partition.setIteratorIndex(sccStartIdx);
        do {
            int i = partition.getValue();
            restriction.set(i);
        } while (partition.nextValid());


//        for (int i = restriction.firstSetBit(); i < arity; i = restriction.nextSetBit(i + 1)) {
//            // 变量只有一个值，即只有匹配值
//            // 若匹配边由变量指向值，若D[x]=1则表示变量x只有一个出边即匹配边，没有入边，即满足singleton条件
////            if (D[i].size() == 1) {
////                varSCC[i] = nbSCC;
////                singleton.set(i);
////                partition.remove(i);
////                restriction.clear(i);
////                nbSCC++;
////            }
//
//            if (!partition.isSingleton(i)) {
//                if (i < arity && D[i].size() == 1) {
//                    varSCC[i] = nbSCC;
//                    singleton.set(i);
//                    partition.remove(i);
//                    restriction.clear(i);
//                    nbSCC++;
//                } else if (i > arity && B[getValueInGraph(i)].size() == 1) {
//                    valSCC[getValueInGraph(i)] = nbSCC;
//                    singleton.set(i);
//                    partition.remove(i);
//                    restriction.clear(i);
//                    nbSCC++;
//                }
//            }
//        }
//        singleton.flip();

//        System.out.println("----------");
//        System.out.println("singleton:" + singleton);
//////////
//        System.out.println("restriction: " + restriction);
////        for (int varIdx = restriction.firstSetBit(); varIdx < arity; varIdx = restriction.nextSetBit(varIdx + 1)) {
//////            if (unVisitedVariables.get(varIdx)) {
//////                System.out.println(varIdx);
////            System.out.printf("out: %d\n", varIdx);
////            strongConnectVar(varIdx);
//////            }
////        }
//        System.out.println("partition: " + partition);
//        for (int varIdx = restriction.firstSetBit(); varIdx < arity; varIdx = restriction.nextSetBit(varIdx + 1)) {
////            if (unVisitedVariables.get(varIdx)) {
////                System.out.println(varIdx);
//            System.out.printf("out: %d\n", varIdx);
//            strongConnectVar(varIdx);
////            }
//        }
//
////        System.out.println(Arrays.toString(varSCC));
////        System.out.println(Arrays.toString(valSCC));
        //////////////////////////
        return findAllSCC_ED();
    }

    boolean findAllSCC_ED() {
        clearVarStack();
        clearValStack();

        findSingletons();
//        System.out.println("restriction: " + restriction);
//        System.out.println("partition: " + partition);
        for (int varIdx = restriction.firstSetBit(); varIdx < arity; varIdx = restriction.nextSetBit(varIdx + 1)) {
//            if (unVisitedVariables.get(varIdx)) {
//                System.out.println(varIdx);
//            System.out.printf("out: %d\n", varIdx);
            cycles.clear();
            if (strongConnectVar(varIdx)) {
                return true;
            }
//            }
        }
        return false;
    }


    private void findSingletons() {

        for (int i = 0; i < arity; i++) {
            // 变量只有一个值，即只有匹配值
            // 若匹配边由变量指向值，若D[x]=1则表示变量x只有一个出边即匹配边，没有入边，即满足singleton条件
//            if (!partition.isSingleton(i) && D[i].size() == 1) {
            if (D[i].size() == 1) {
                varSCC[i] = nbSCC;
                singleton.set(i);
                restriction.clear(i);
                partition.remove(i);
                nbSCC++;
            }
        }
    }

    private boolean strongConnectVar(int curNode) {
        System.out.println("scvr: " + curNode + ", " + maxDFS);
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
                ////// DE
//                System.out.println("DETest valLowLink: " + valLowLink[newNode] + ", node: " + newNode + ", dfs: " + (maxDFS - 1) + " unconnected: " + unconnected + " DE Size: " + DE.size());
                if (numCall != 0) DETest(valLowLink[newNode], maxDFS - 1);
            }

            values = D[curNode].getWord(iWord) & unVisitedValues.getWord(iWord);
            for (i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
                newNode = iBase + i;
                if (strongConnectVal(newNode)) {
                    return true;
                }
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

        if (!unconnected && (DE.size() == 0)) {
//            System.out.println("xixi");
            return true;
        }
        return false;
//        System.out.println("back");
    }

    private boolean strongConnectVal(int curNode) {
        System.out.println("scvl: " + curNode + ", " + maxDFS);
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
//                    System.out.println("DETest varLowLink: " + varLowLink[matchedVar] + ", node: " + matchedVar + ", dfs: " + (maxDFS - 1) + " unconnected: " + unconnected + " DE Size: " + DE.size());
                    if (numCall != 0) DETest(varLowLink[matchedVar], maxDFS - 1);
                }
            } else {
                if (strongConnectVar(matchedVar)) {
                    return true;
                }
                valLowLink[curNode] = Math.min(valLowLink[curNode], varLowLink[matchedVar]);
            }
        } else {
            //free node successor node is sink node
//            System.out.println("scValtoSink: " + (addArity + curNode) + ", " + arity + ", " + sinkIsUnvisited);
//            System.out.println((addArity + curNode) + ", " + arity + ", " + sinkIsUnvisited);
            if (!sinkIsUnvisited) {
                if (sinkIsInStack) {
                    valLowLink[curNode] = Math.min(valLowLink[curNode], sinkDFSNum);
//                    System.out.println("DETest sinkLowLink: " + sinkLowLink + ", node: sink, dfs: " + (maxDFS - 1) + " unconnected: " + unconnected + " DE Size: " + DE.size());
                    if (numCall != 0) DETest(sinkLowLink, maxDFS - 1);
                }
            } else {
                if (strongConnectSink()) {
                    return true;
                }
                valLowLink[curNode] = Math.min(valLowLink[curNode], sinkLowLink);
            }
        }

        if (valLowLink[curNode] == valDFSNum[curNode]) {
            if (valLowLink[curNode] > 0 || valIsInStack.size() + varIsInStack.size() > 0) {
                hasSCCSplit = true;
            }
            if (hasSCCSplit) {
                processSCC(valDFSNum[curNode]);
            }
        }

        if (!unconnected && (DE.size() == 0)) {
//            System.out.println("xixi");
            return true;
        }

        return false;
    }

    private boolean strongConnectSink() {
        System.out.println("scs: " + ", " + maxDFS);
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
//                    System.out.println("DETest valLowLink: " + valLowLink[newNode] + ", node: " + newNode + ", dfs: " + (maxDFS - 1) + " unconnected: " + unconnected + " DE Size: " + DE.size());
                    if (numCall != 0) DETest(valLowLink[newNode], maxDFS - 1);
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
//                int stackNode = -1;
//                sccSize = 0;
//                while (stackNode != curNode) {
//                    stackNode = popStack();
////                    System.out.println("pop: " + stackNode + ", " + nbSCC);
//                    nodeSCC[stackNode] = nbSCC;
//                    sccSize++;
//                }
////                if (sccSize == 1) {
////                    singleton.add(nbSCC);
////                }
//                nbSCC++;
                processSCC(sinkDFSNum);
            }
        }
//        System.out.println("back");
        if (!unconnected && (DE.size() == 0)) {
//            System.out.println("xixi");
            return true;
        }
        return false;
    }

    private void processSCC(int rootNum) {
//        for (int valIdx = valIsInStack.firstSetBit(); valIdx !=INaiveBitSet.INDEX_OVERFLOW; valIdx=valIsInStack.++) {
//
//        }
//        System.out.println("scc: " + rootNum);
        int stackNode = -1;
        sccSize = 0;
        int limit;

        if (varStackIdx > 0 && varDFSNum[varStack[varStackIdx - 1]] >= rootNum) {
            int x = getTopVarStack();
            limit = partition.resetLimitByElement(x);
        } else if (valStackIdx > 0 && valDFSNum[valStack[valStackIdx - 1]] >= rootNum) {
            int x = getTopValStack();
            limit = partition.resetLimitByElement(getValueIndexInGraph(x));
        }

//        if (valStackIdx != 0) {
//            stackNode = valStack[valStackIdx - 1];
        while (valStackIdx > 0 && valDFSNum[valStack[valStackIdx - 1]] >= rootNum) {
            stackNode = popValStack();
//            System.out.println("pop var: " + stackNode + ", " + nbSCC + "," + valDFSNum[stackNode]);
            valSCC[stackNode] = nbSCC;
            partition.add(getValueIndexInGraph(stackNode));
            restriction.clear(getValueIndexInGraph(stackNode));
            sccSize++;
        }
//        }

//        if (varStackIdx != 0) {
//            stackNode = varStack[varStackIdx - 1];
        while (varStackIdx > 0 && varDFSNum[varStack[varStackIdx - 1]] >= rootNum) {
            stackNode = popVarStack();
//            System.out.println("pop val: " + stackNode + ", " + addArity + stackNode + ", " + nbSCC + "," + varDFSNum[stackNode]);
            varSCC[stackNode] = nbSCC;
            restriction.clear(stackNode);
            partition.add(stackNode);
            singleton.clear(stackNode);
            sccSize++;
        }
//        }

        if (sinkIsInStack && sinkDFSNum >= rootNum) {
            partition.add(arity);
            restriction.clear(arity);
            sinkIsInStack = false;
        }

        partition.setSplit();
        nbSCC++;

        unconnected = true;
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

    private int getTopVarStack() {
        return varStack[varStackIdx - 1];
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

    private int getTopValStack() {
        return valStack[valStackIdx - 1];
    }

    public void getIntTuple2(IntTuple2 vvp, long vvpIdx) {
        vvp.a = (int) (vvpIdx >> INT_SIZE);
        vvp.b = (int) vvpIdx;
    }

    public IntTuple2 getIntTuple2(long vvpIdx) {
        return new IntTuple2((int) (vvpIdx >> INT_SIZE), (int) vvpIdx);
    }

    public long getIntTuple2Long(int x, int a) {
        long c = (long) x;
        return c << INT_SIZE | a;
    }

    public int nextSetBit(long words, int bitIndex) {
        return Long.numberOfTrailingZeros(words & -1L << bitIndex);
    }

    private int getValueIndexInGraph(int value) {
        return value + addArity;
    }

    private int getValueInGraph(int valueIndex) {
        return valueIndex - addArity;
    }

    private void getAllSCCStartIndices(TIntHashSet sccStartIndex) {
        partition.getSCCStartIndex(sccStartIndex);
    }

    private void DETest(int lowLinkNewNode, int dfs) {
        System.out.println("DETest: " + lowLinkNewNode + ", " + dfs + " unconnected: " + unconnected + " DE Size: " + DE.size());
        if (!unconnected) {
            cycles.add(lowLinkNewNode, dfs);

            while (!(DE.size() == 0) && inCycles(DE.peek())) {
                DE.pop();
            }
        }
    }

    private boolean inCycles(long f) {
//        IntTuple2 tt;
        getIntTuple2(nodePair, f);
        System.out.println("inc:" + nodePair.a + "," + nodePair.b + "=" + varDFSNum[nodePair.a] + "," + valDFSNum[nodePair.b]);
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

//    private boolean inCycles(long f) {
////        IntTuple2 tt;
//        getIntTuple2(nodePair, f);
//        System.out.println("inc:" + nodePair.a + "," + nodePair.b + "=" + varDFSNum[nodePair.a] + "," + valDFSNum[nodePair.b]);
//        int a, b;
//        if (varDFSNum[nodePair.a] <= valDFSNum[nodePair.b]) {
//            a = varDFSNum[nodePair.a];
//            b = valDFSNum[nodePair.b];
//        } else {
//            a = valDFSNum[nodePair.b];
//            b = varDFSNum[nodePair.a];
//        }
//        if (a == Integer.MAX_VALUE || b == Integer.MAX_VALUE) {
//            return false;
//        }
//
//        if (cycles.contains(a, b)) {
//            return true;
//        }
//
//        return false;
//    }


}