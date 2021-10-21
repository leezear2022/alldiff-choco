package org.chocosolver.solver.constraints.nary.alldifferent.algo;

//import org.chocosolver.amtf.Measurer;

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.map.hash.TIntIntHashMap;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.INaiveBitSet;
import org.chocosolver.util.objects.Measurer;
import org.chocosolver.util.objects.SparseSet;

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
public class AlgoAllDiffAC_NaiveBitSetNewBack extends AlgoAllDiffAC_Naive {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************
    // 约束的个数
    static public int num = 0;

    // 约束的编号
    private int id;
    private long xixi = 0;

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
    // 值到索引
    private int[] idx2Val;
    // 索引到值
    private TIntIntHashMap val2Idx;

    // Xc-Γ(A)
    private SparseSet notGamma;
    // Dc-A
    private SparseSet notA;

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
    private INaiveBitSet matchedMasks;

    private INaiveBitSet varSingletonMask;
    private INaiveBitSet valSingletonMask;
    private INaiveBitSet varTmpMask;
    // matching
    private int[] val2Var;
    private int[] var2Val;

    // 记录队列
    private int[] visiting_;
    private int[] variable_visited_from_;

    // 变量到变量的连通性
    // 对于惰性算法，记录是否知道-变量到变量的连通性
    private INaiveBitSet[] graphLinkedMatrix;
    private INaiveBitSet[] graphLinkedFrontier;

    // !! 记录gamma的前沿
    private INaiveBitSet gammaFrontier;
    // 记录gamma的bitset
    private INaiveBitSet gammaMask;

    long startTime;


    private int endBitIndex = 64;

    // for delta update
//    protected IIntDeltaMonitor[] monitors;
//    private UnaryIntProcedure<Integer> onValRem;
//    private boolean initialProp = true;
//
//    //    // for backtrack
//    IEnvironment env;
//    IStateBitSet[] RB;
//    IStateBitSet[] RD;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_NaiveBitSetNewBack(IntVar[] variables, ICause cause, Model model) {
        super(variables, cause);
        id = num++;
//        env = model.getEnvironment();
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

//        System.out.println("-----------idx2Val-----------");
//        System.out.println(Arrays.toString(idx2Val));
//for backtracking
        B = new INaiveBitSet[numValues];
//        RB = new IStateBitSet[numValues];

        for (int i = 0; i < numValues; ++i) {
            B[i] = INaiveBitSet.makeBitSet(arity, false);
//            RB[i] = env.makeBitSet(arity);
        }

        D = new INaiveBitSet[arity];
//        RD = new IStateBitSet[arity];
        for (int i = 0; i < arity; ++i) {
            D[i] = INaiveBitSet.makeBitSet(numValues, false);
//            RD[i] = env.makeBitSet(numValues);
        }

        // 填充B和D
        for (int i = 0; i < arity; ++i) {
            v = vars[i];
            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
                int valIdx = val2Idx.get(j);
                D[i].set(valIdx);
//                RD[i].set(valIdx);
                B[valIdx].set(i);
//                RB[valIdx].set(i);
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
        matchedMasks = INaiveBitSet.makeBitSet(numValues, true);
        varSingletonMask = INaiveBitSet.makeBitSet(arity, false);
        valSingletonMask = INaiveBitSet.makeBitSet(numValues, false);
        varTmpMask = INaiveBitSet.makeBitSet(arity, false);

        var2Val = new int[arity];
        val2Var = new int[numValues];
        for (int i = 0; i < arity; ++i) {
            var2Val[i] = -1;
        }
        for (int i = 0; i < numValues; ++i) {
            val2Var[i] = -1;
        }

        freeNode = new SparseSet(numValues);
        gammaFrontier = INaiveBitSet.makeBitSet(arity, false);
        gammaMask = INaiveBitSet.makeBitSet(arity, false);
        notGamma = new SparseSet(arity);
        notA = new SparseSet(numValues);

        graphLinkedMatrix = new INaiveBitSet[arity];
        graphLinkedFrontier = new INaiveBitSet[arity];
        for (int i = 0; i < arity; ++i) {
            graphLinkedMatrix[i] = INaiveBitSet.makeBitSet(arity, false);
            graphLinkedFrontier[i] = INaiveBitSet.makeBitSet(arity, false);
        }

        // for delta
//        monitors = new IIntDeltaMonitor[vars.length];
//        for (int i = 0; i < vars.length; i++) {
//            monitors[i] = vars[i].monitorDelta(cause);
//        }
//        onValRem = makeProcedure();
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    public boolean propagate() throws ContradictionException {
        Measurer.enterProp();
        startTime = System.nanoTime();
        fillBandD();
        findMaximumMatching();
        Measurer.matchingTime += System.nanoTime() - startTime;

        startTime = System.nanoTime();
        boolean filter = filter();
        Measurer.filterTime += System.nanoTime() - startTime;
        return filter;
    }

    //***********************************************************************************
    // Initialization
    //***********************************************************************************


//    protected UnaryIntProcedure<Integer> makeProcedure() {
//        return new UnaryIntProcedure<Integer>() {
//            int var;
//            int valIdx;
//
//            @Override
//            public UnaryIntProcedure set(Integer o) {
//                var = o;
//                return this;
//            }
//
//            @Override
//            public void execute(int i) throws ContradictionException {
////                DE.push(new IntTuple2(var, val2Idx.get(i) + addArity));
////                IntVar v = vars[var];
//                valIdx = val2Idx.get(i);
//                RD[var].clear(valIdx);
//                RB[valIdx].clear(var);
////                System.out.println(vars[var].getName() + "," + var + ", " + i + " = " + v.contains(i) + ", size = " + v.getDomainSize());
//            }
//        };
//    }

    private void printDomains() {
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

//    private void fillRBandRD(int varIdx) {
////        for (int i = 0; i < numValues; ++i) {
////            B[varIdx].clear();
//
//        IntVar v;
//        // 填充RB和RD
////        for (int i = 0; i < arity; ++i) {
//        RD[varIdx].clear();
//        v = vars[varIdx];
//        for (int i = 0; i < numValues; ++i) {
//            int val = idx2Val[i];
//            if (v.contains(val)) {
//                RD[varIdx].set(i);
//                RB[i].set(varIdx);
//            } else {
//                RB[i].clear(varIdx);
//            }
//        }
//    }

//    private void deltaUpdate() throws ContradictionException {
//        for (int varIdx = 0; varIdx < arity; varIdx++) {
//            monitors[varIdx].freeze();
//            if (vars[varIdx].getDomainSize() > monitors[varIdx].sizeApproximation()) {
//                monitors[varIdx].forEachRemVal(onValRem.set(varIdx));
//            } else {
//                fillRBandRD(varIdx);
//            }
//            D[varIdx].set(RD[varIdx]);
//            monitors[varIdx].unfreeze();
//        }
//
//        for (int i = 0; i < numValues; ++i) {
//            B[i].set(RB[i]);
//        }
//
//    }

    private boolean BandDCheck() {
        IntVar v;
        for (int i = 0; i < arity; ++i) {
            v = vars[i];
            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
                int valIdx = val2Idx.get(j);
                if (!D[i].get(valIdx)) {
                    System.out.println("D[" + i + "] no contain but var: " + v.getName() + " contain:" + valIdx);
                    return false;
                }
            }

            for (int j = D[i].firstSetBit(); j != D[i].end(); j = D[i].nextSetBit(j + 1)) {
                if (!v.contains(idx2Val[j])) {
                    System.out.println("D[" + i + "] contain but var: " + v.getName() + "don't contain:" + j);
                    return false;
                }
            }
        }

        return true;
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
//        // !! 可做增量
//        for (int i = 0; i < numValues; ++i) {
//            B[i].clear();
//        }

//        freeNode.set();
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

    private void distinguish() {
        notGamma.fill();
        notA.fill();
        gammaMask.clear();

        freeNode.iterateValid();
        while (freeNode.hasNextValid()) {
            // 每个freeNode的值拿出来
//            System.out.println(i);
            int valIdx = freeNode.next();
            notA.remove(valIdx);
            gammaMask.or(B[valIdx]);
        }
        gammaFrontier.set(gammaMask);

        for (int varIdx = gammaFrontier.nextSetBit(0);
             varIdx != gammaFrontier.end(); varIdx = gammaFrontier.nextSetBit(0)) {
            // !! 这里可以将Extended改成Frontier，只记录前沿，记录方法是三个BitSet比较，
            // frontier 扩展，从valMask中去掉gammaMask已记录的变量
            int valIdx = var2Val[varIdx];
            gammaFrontier.orAfterMinus(B[valIdx], gammaMask);
//            // 除去第i个变量
            gammaFrontier.clear(varIdx);
            // gamma 扩展
            gammaMask.or(B[valIdx]);
            notGamma.remove(varIdx);
            notA.remove(valIdx);
        }

    }

    private void initiateMatrix() {
        // 重置两个矩阵
        // 只重置notGamma的变量
        notGamma.iterateValid();
        while (notGamma.hasNextValid()) {
            int varIdx = notGamma.next();
            // 从变量id拿到匹配值再拿到该值所能到达的变量mask
            if (!vars[varIdx].isInstantiated()) {
                graphLinkedMatrix[varIdx].setAfterMinus(B[var2Val[varIdx]], gammaMask);
                graphLinkedMatrix[varIdx].clear(varIdx);
                graphLinkedFrontier[varIdx].set(graphLinkedMatrix[varIdx]);
            }
//                System.out.println("------graphLinkedMatrix[" + varIdx + "]------");
//                System.out.println(graphLinkedMatrix[varIdx]);
//                System.out.println(graphLinkedFrontier[varIdx]);
        }
    }

    private boolean filter() throws ContradictionException {
        distinguish();
        initiateMatrix();
        // 这里判断一下，如果notGamma为空则不用进行如下步骤
        boolean filter = false;
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            IntVar v = vars[varIdx];
            if (!v.isInstantiated()) {
                for (int valIdx = D[varIdx].firstSetBit(); valIdx != D[varIdx].end(); valIdx = D[varIdx].nextSetBit(valIdx + 1)) {
                    int k = idx2Val[valIdx];
//                    System.out.println(valIdx);
                    if (!notGamma.contains(varIdx) && notA.contains(valIdx)) {
                        ++Measurer.numDelValuesP1;
                        Measurer.enterP1();
//                        D[varIdx].clear(valIdx);
                        filter |= v.removeValue(k, aCause);
                        //                System.out.println("first delete: " + v.getName() + ", " + k);
                    } else if (notGamma.contains(varIdx) && notA.contains(valIdx)) {
                        if (!graphLinkedMatrix[varIdx].get(val2Var[valIdx]) && !checkSCC(varIdx, valIdx)) {
                            Measurer.enterP2();
                            if (valIdx == var2Val[varIdx]) {
                                int valNum = v.getDomainSize();
                                Measurer.numDelValuesP2 += valNum - 1;
                                filter |= v.instantiateTo(k, aCause);
//                            System.out.println("instantiate  : " + v.getName() + ", " + k);
                            } else {
                                ++Measurer.numDelValuesP2;
                                filter |= v.removeValue(k, aCause);
//                            System.out.println("second delete: " + v.getName() + ", " + k);
                            }
                        }
                    }
                }
            }
        }
        return filter;
    }

    private boolean checkSCC(int varIdx, int valIdx) {
//        System.out.println("check:" + varIdx + ", " + valIdx);
        // 若没有 就需要BFS一下Frontier没有，就表示不用扩展了
        // 注意一下return退出时frontier正确
        for (int i = graphLinkedFrontier[varIdx].nextSetBit(0);
             i != graphLinkedFrontier[varIdx].end(); i = graphLinkedFrontier[varIdx].nextSetBit(0)) {
            // frontier扩张，除掉变量i 因为变量i已被扩展。
            graphLinkedFrontier[varIdx].orAfterMinus(graphLinkedMatrix[i], graphLinkedMatrix[varIdx]);
            graphLinkedFrontier[varIdx].clear(i);
            graphLinkedMatrix[varIdx].or(graphLinkedMatrix[i]);
            if (graphLinkedMatrix[varIdx].get(val2Var[valIdx])) {
                return true;
            }
        }
        return false;
    }
}