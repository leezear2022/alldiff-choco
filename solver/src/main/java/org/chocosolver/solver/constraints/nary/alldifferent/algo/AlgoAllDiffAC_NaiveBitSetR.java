package org.chocosolver.solver.constraints.nary.alldifferent.algo;

//import org.chocosolver.amtf.Measurer;

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.map.hash.TIntIntHashMap;
import org.chocosolver.memory.IStateLong;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
import org.chocosolver.util.objects.IntTuple2;
import org.chocosolver.util.objects.Measurer;
import org.chocosolver.util.objects.NaiveBitSet;
import org.chocosolver.util.objects.SparseSet;
import org.chocosolver.util.procedure.UnaryIntProcedure;

import java.util.Stack;

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
public class AlgoAllDiffAC_NaiveBitSetR {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************
    // 约束的个数
    static public int num = 0;
    // 约束的编号
    private int id;

    private int arity;
    private IntVar[] vars;
    private ICause aCause;

    // 自由值集合
    private SparseSet freeNode;

    // 以下是bit版本所需数据结构========================
    // numValue是二部图中取值编号的个数，numBit是二部图的最大边数
    private int numValue;
    // 值到索引
    private int[] idx2Val;
    // 索引到值
    private TIntIntHashMap val2Idx;

    // Xc-Γ(A)
    private SparseSet notGamma;
    // Dc-A
    private SparseSet notA;


    // 已访问过的变量和值
    private NaiveBitSet variable_visited_;
    private NaiveBitSet value_visited_;

    // matching
    private int[] val2Var;
    private int[] var2Val;

    // 记录队列
    private int[] visiting_;
    private int[] variable_visited_from_;

    // 变量到变量的连通性
    // 对于惰性算法，记录是否知道-变量到变量的连通性
    private NaiveBitSet[] graphLinkedMatrix;
    private NaiveBitSet[] graphLinkedFrontier;

    // !! 记录gamma的前沿
    private NaiveBitSet gammaFrontier;
    // 记录gamma的bitset
    private NaiveBitSet gammaMask;

    //用于回溯
    private IStateLong[][] RDbit;
    private IStateLong[][] RBbit;

    // 与值相连的变量
    private NaiveBitSet[] Bbit;
    // bit论域
    private NaiveBitSet[] Dbit;

    // for delta update
    protected IIntDeltaMonitor[] monitors;
    private UnaryIntProcedure<Integer> onValRem;
    private boolean initialProp = true;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_NaiveBitSetR(IntVar[] variables, ICause cause, Model model) {
//        super(variables, cause);
        id = num++;

        this.vars = variables;
        aCause = cause;
        arity = vars.length;
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

        numValue = val2Idx.size();
        idx2Val = new int[numValue];
        TIntIntIterator it = val2Idx.iterator();
        while (it.hasNext()) {
            it.advance();
            idx2Val[it.value()] = it.key();
        }

//        System.out.println("-----------idx2Val-----------");
//        System.out.println(Arrays.toString(idx2Val));

        // bit向量化D和B 与RD和RB
        Bbit = new NaiveBitSet[numValue];
        RBbit = new IStateLong[numValue][];
        for (int i = 0; i < numValue; ++i) {
            Bbit[i] = new NaiveBitSet(arity);
            int BLongSize = Bbit[i].longSize();
            RBbit[i] = new IStateLong[BLongSize];
            for (int j = 0; j < BLongSize; j++) {
                RBbit[i][j] = model.getEnvironment().makeLong(0L);
            }
        }

        Dbit = new NaiveBitSet[arity];
        RDbit = new IStateLong[arity][];
        int valSize = val2Idx.size();
        for (int i = 0; i < arity; i++) {
            Dbit[i] = new NaiveBitSet(valSize);
            int DLongSize = Dbit[i].longSize();
            RDbit[i] = new IStateLong[DLongSize];
            for (int j = 0; j < DLongSize; j++) {
                RDbit[i][j] = model.getEnvironment().makeLong(0L);
            }
        }

        for (int i = 0; i < arity; ++i) {
            v = vars[i];
            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
                int valIdx = val2Idx.get(j);
                Bbit[valIdx].set(i);
                Dbit[i].get(valIdx);
            }

            int DLongSize = Dbit[i].longSize();
            int BLongSize = Bbit[i].longSize();

            for (int j = 0; j < DLongSize; j++) {
                RDbit[i][j].set(Dbit[i].words(j));
            }

            for (int j = 0; j < BLongSize; j++) {
                RBbit[i][j].set(Bbit[i].words(j));
            }
        }

        // 记录访问过的变量
        visiting_ = new int[arity];
        variable_visited_ = new NaiveBitSet(arity);
        // 变量的前驱变量，若前驱变量是-1，则表示无前驱变量，就是第一个变量
        variable_visited_from_ = new int[arity];
        value_visited_ = new NaiveBitSet(numValue);

        var2Val = new int[arity];
        val2Var = new int[numValue];
        for (int i = 0; i < arity; ++i) {
            var2Val[i] = -1;
        }
        for (int i = 0; i < numValue; ++i) {
            val2Var[i] = -1;
        }

        freeNode = new SparseSet(numValue);
        gammaFrontier = new NaiveBitSet(arity);
        gammaMask = new NaiveBitSet(arity);
        notGamma = new SparseSet(arity);
        notA = new SparseSet(numValue);

        graphLinkedMatrix = new NaiveBitSet[arity];
        graphLinkedFrontier = new NaiveBitSet[arity];
        for (int i = 0; i < arity; ++i) {
            graphLinkedMatrix[i] = new NaiveBitSet(arity);
            graphLinkedFrontier[i] = new NaiveBitSet(arity);
        }
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    public boolean propagate() throws ContradictionException {
        Measurer.enterProp();
        long startTime = System.nanoTime();
        findMaximumMatching();
        Measurer.matchingTime += System.nanoTime() - startTime;

        startTime = System.nanoTime();
        boolean filter = filter();
        Measurer.filterTime += System.nanoTime() - startTime;
        return filter;
    }

    protected UnaryIntProcedure<Integer> makeProcedure() {
        return new UnaryIntProcedure<Integer>() {
            int var;

            @Override
            public UnaryIntProcedure set(Integer o) {
                var = o;
                return this;
            }

            @Override
            public void execute(int i) throws ContradictionException {
//                Bbit = RBbit[var]
//                DE.push(new IntTuple2(var, val2Idx.get(i) + addArity));
//                IntVar v = vars[var];
//                System.out.println(vars[var].getName() + "," + var + ", " + i + " = " + v.contains(i) + ", size = " + v.getDomainSize());
            }
        };
    }

    //***********************************************************************************
    // Initialization
    //***********************************************************************************

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
        variable_visited_.set(start);
        variable_visited_from_[start] = -1;

        while (num_visited < num_to_visit) {
            // Dequeue node to visit.
            int node = visiting_[num_visited++];
            IntVar v = vars[node];

            for (int value = v.getLB(), ub = v.getUB(); value <= ub; value = v.nextValue(value)) {
                int valIdx = val2Idx.get(value);
                if (value_visited_.get(valIdx)) continue;
                value_visited_.set(valIdx);
                if (val2Var[valIdx] == -1) {
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
//                    System.out.println(valIdx + " is not free");
                    return;
                } else {
                    // Enqueue node matched to valIdx.
                    // 若没有该值已经有匹配，但变量没有匹配

                    // 先拿到这个值的匹配变量
                    int next_node = val2Var[valIdx];
                    variable_visited_.set(next_node);
//                    System.out.println(num_to_visit + "," + next_node);
                    // 把这个变量加入队列中
                    visiting_[num_to_visit++] = next_node;
                    variable_visited_from_[next_node] = node;
//                    freeNode.clear(valIdx);
                    freeNode.remove(valIdx);
                }
            }
        }
    }

    private void findMaximumMatching() throws ContradictionException {
        // !! 可做增量
        for (int i = 0; i < numValue; ++i) {
            Bbit[i].clear();
        }

//        freeNode.set();
        freeNode.fill();

        // 增量检查
        // matching 有效性检查
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            IntVar v = vars[varIdx];
            // !! 这里可以修改一下 已赋值 就不参与修改了
            if (v.getDomainSize() == 1) {
                // 取出变量的唯一值
                int valIdx = val2Idx.get(v.getValue());
                Bbit[valIdx].set(varIdx);
//                System.out.println(v.getName() + " : " + varIdx + " is singleton = " + v.getValue() + " : " + valIdx);

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

            } else {
                // 检查原匹配是否失效
                int oldMatchingIndex = var2Val[varIdx];
                if (oldMatchingIndex != -1) {
                    // 如果oldMatchingValue无效
                    if (!v.contains(idx2Val[oldMatchingIndex])) {
                        val2Var[oldMatchingIndex] = -1;
                        var2Val[varIdx] = -1;
                    } else {
//                        freeNode.clear(oldMatchingIndex);
                        freeNode.remove(oldMatchingIndex);
//                    System.out.println(oldMatchingIndex + " is free");
                    }
                }

                for (int value = v.getLB(), ub = v.getUB(); value <= ub; value = v.nextValue(value)) {
                    int valIdx = val2Idx.get(value);
                    // Forward-checking should propagate xsu != value.
                    // !! 可以增量修改值
                    Bbit[valIdx].set(varIdx);
                }
            }
        }

        // Compute max matching.
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            if (var2Val[varIdx] == -1) {
                value_visited_.clear();
                variable_visited_.clear();
                MakeAugmentingPath(varIdx);
            }
            if (var2Val[varIdx] == -1) {
                // No augmenting path exists.
                vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
            }
        }
//        if (id == 2) {
//            System.out.println("-----final matching-----");
//            for (int i = 0; i < arity; i++) {
//                System.out.println(vars[i].getName() + " match " + idx2Val[var2Val[i]]);
//            }
//            System.out.println("------------------");
//        }
//        System.out.println(Arrays.toString(var2Val));
//        System.out.println(Arrays.toString(val2Var));
//        System.out.println(freeNode);
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
            gammaMask.or(Bbit[valIdx]);
        }
        gammaFrontier.set(gammaMask);

        for (int varIdx = gammaFrontier.nextSetBit(0);
             varIdx != -1; varIdx = gammaFrontier.nextSetBit(0)) {
            // !! 这里可以将Extended改成Frontier，只记录前沿，记录方法是三个BitSet比较，
            // frontier 扩展，从valMask中去掉gammaMask已记录的变量
            int valIdx = var2Val[varIdx];
            gammaFrontier.orAfterMinus(Bbit[valIdx], gammaMask);
//            // 除去第i个变量
            gammaFrontier.clear(varIdx);
            // gamma 扩展
            gammaMask.or(Bbit[valIdx]);
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
                graphLinkedMatrix[varIdx].setAfterMinus(Bbit[var2Val[varIdx]], gammaMask);
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
                int ub = v.getUB();
                for (int k = v.getLB(); k <= ub; k = v.nextValue(k)) {
                    int valIdx = val2Idx.get(k);
                    if (!notGamma.contain(varIdx) && notA.contain(valIdx)) {
                        ++Measurer.numDelValuesP1;
                        Measurer.enterP1();
                        filter |= v.removeValue(k, aCause);
                        //                System.out.println("first delete: " + v.getName() + ", " + k);
                    } else if (notGamma.contain(varIdx) && notA.contain(valIdx)) {
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
             i != -1; i = graphLinkedFrontier[varIdx].nextSetBit(0)) {
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