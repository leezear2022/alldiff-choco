package org.chocosolver.solver.constraints.nary.alldifferent.algo;

//import org.chocosolver.amtf.Measurer;
import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.map.hash.TIntIntHashMap;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.Measurer;
import org.chocosolver.util.objects.NaiveBitSet;
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
public class AlgoAllDiffAC_Naive64 extends AlgoAllDiffAC_Naive {

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
    private long variable_visited_;
    private NaiveBitSet value_visited_;

    // matching
    private int[] val2Var;
    private int[] var2Val;

    // 记录队列
    private int[] visiting_;
    private int[] variable_visited_from_;

    // 变量到变量的连通性
    // 对于惰性算法，记录是否知道-变量到变量的连通性
    private long[] graphLinkedMatrix;
    private long[] graphLinkedFrontier;

    // !! 记录gamma的前沿
    private long gammaFrontier;
    // 记录gamma的bitset
    private long gammaMask;

    // 变量的论域
    private long[] valMask;

    // 内置的bit方法专用的常量
    protected long lastMask;

    protected final static int ADDRESS_BITS_PER_WORD = 6;
    protected final static int BITS_PER_WORD = 1 << ADDRESS_BITS_PER_WORD;
    //    protected final static int BIT_INDEX_MASK = BITS_PER_WORD - 1;
    /* Used to shift left or right for a partial word mask */
    protected static final long WORD_MASK = 0xffffffffffffffffL;
//    protected static final long MOD_MASK = 0x3fL;
//    protected static final int MOD_MASK_INT = 0x3f;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_Naive64(IntVar[] variables, ICause cause) {
        super(variables, cause);
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

        valMask = new long[numValue];

        // 记录访问过的变量
        visiting_ = new int[arity];
        variable_visited_ = 0L;
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

        notGamma = new SparseSet(arity);
        notA = new SparseSet(numValue);
        freeNode = new SparseSet(numValue);
        gammaFrontier = 0L;
        gammaMask = 0L;

        graphLinkedMatrix = new long[arity];
        graphLinkedFrontier = new long[arity];

        this.lastMask = WORD_MASK >>> (BITS_PER_WORD - arity);
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    public boolean propagate() throws ContradictionException {
//        if (id == 2) {
//            System.out.println("vars: ");
//            for (IntVar v : vars) {
//                System.out.println(v.toString());
//            }
//        }
        Measurer.enterProp();
        long startTime = System.nanoTime();
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

    private void MakeAugmentingPath(int start) {
        // Do a BFS and use visiting_ as a queue, with num_visited pointing
        // at its begin() and num_to_visit its end().
        // To switch to the augmenting path once a nonmatched value was found,
        // we remember the BFS tree in variable_visited_from_.

        // start传入的是变量
        // 执行一个BFS并使用visiting_作为一个队列，num_visited指向它的begin()，
        // num_to_visit指向它的end()。要在发现不匹配的值时切换到扩展路径，
        // 我们需要记住variable_visited_from_中的BFS树
        int num_to_visit = 0;
        int num_visited = 0;
        // Enqueue start.
        // visit 里存的是变量
        visiting_[num_to_visit++] = start;
//        variable_visited_[start] = true;
//        variable_visited_.set(start);
        variable_visited_ |= 1L << start;
        variable_visited_from_[start] = -1;
        IntVar v;
        while (num_visited < num_to_visit) {
            // Dequeue node to visit.
            int node = visiting_[num_visited++];
            v = vars[node];
//            for (int value = varMask[node].nextSetBit(0); value != -1; value = varMask[node].nextSetBit(value + 1)) {
            for (int val = v.getLB(), ub = v.getUB(); val <= ub; val = v.nextValue(val)) {
                int value = val2Idx.get(val);
//                valMask[value] |= 1L << node;
//                valMask[value] |= 1L << varIdx;
                if (value_visited_.get(value)) continue;
                value_visited_.set(value);
                if (val2Var[value] == -1) {
                    // value_to_variable_[value] ， value这个值未分配到变量，即是一个free
                    // !! 这里可以改用bitSet 求原数据bitDom (successor_)
                    // 与matching的余集(matching_bitVector[a]，表示a是否已matching出去了) 再按1取未匹配值，
                    // 可以惰性取值，即先算两个集合的在特定位置的交：以matching_bv为长度foreach
                    // （一般不会特别长两个数据结构可以用NaiveBitSet，如400皇后，|D|=400，只需要7个，
                    // 做&后会得到一个或NaiveBitSet, LargeBitSet）
                    // value is not matched: change path from node to start, and return.
                    // 未匹配值

                    // !! 路线回溯怎么用bit表示。
                    // !! 这里可以提前记一些scc或是路径
                    int path_node = node;
                    int path_value = value;
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

//                    freeNode.clear(value);
                    freeNode.remove(value);
//                    System.out.println(value + " is not free");
                    return;
                } else {
                    // Enqueue node matched to value.
                    // 若没有该值已经有匹配，但变量没有匹配

                    // 先拿到这个值的匹配变量
                    int next_node = val2Var[value];
//                    variable_visited_.set(next_node);
                    variable_visited_ |= 1L << next_node;
//                    System.out.println(num_to_visit + "," + next_node);
                    // 把这个变量加入队列中
                    visiting_[num_to_visit++] = next_node;
                    variable_visited_from_[next_node] = node;
//                    freeNode.clear(value);
                    freeNode.remove(value);
                }
            }
        }
    }

    private void findMaximumMatching() throws ContradictionException {
        // !! 可做增量
        for (int i = 0; i < numValue; ++i) {
            valMask[i] = 0L;
        }

        freeNode.fill();

        // 增量检查
        // matching 有效性检查
        for (int varIdx = 0; varIdx < arity; varIdx++) {
//            varMask[varIdx].clear();
            IntVar v = vars[varIdx];
            // !! 这里可以修改一下 已赋值 就不参与修改了
            if (v.getDomainSize() == 1) {
                // 取出变量的唯一值
                int valIdx = val2Idx.get(v.getValue());
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
                        freeNode.remove(oldMatchingIndex);
                    }
                }

                for (int value = v.getLB(), ub = v.getUB(); value <= ub; value = v.nextValue(value)) {
                    int valIdx = val2Idx.get(value);
                    // Forward-checking should propagate xsu != value.
                    valMask[valIdx] |= 1L << varIdx;
                }
            }
        }

        // Compute max matching.
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            if (var2Val[varIdx] == -1) {
                value_visited_.clear();
//                variable_visited_.clear();
                variable_visited_ = 0L;
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
        gammaMask = 0L;

        freeNode.iterateValid();
        while (freeNode.hasNextValid()) {
            int i = freeNode.next();
            notA.remove(i);
            gammaMask |= valMask[i];
        }
        gammaFrontier = gammaMask;

        for (int varIdx = nextSetBit(gammaFrontier, 0);
             varIdx != BITS_PER_WORD; varIdx = nextSetBit(gammaFrontier, 0)) {
            int valIdx = var2Val[varIdx];
            gammaFrontier |= valMask[valIdx] & ~gammaMask;
            // 除去第i个变量
            gammaFrontier &= ~(1L << varIdx);
            // gamma 扩展
            gammaMask |= valMask[valIdx];
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
                graphLinkedMatrix[varIdx] = valMask[var2Val[varIdx]] & ~gammaMask;
                graphLinkedMatrix[varIdx] &= ~(1L << varIdx);
                graphLinkedFrontier[varIdx] = graphLinkedMatrix[varIdx];
            }
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
                        if ((graphLinkedMatrix[varIdx] & 1L << val2Var[valIdx]) == 0L && !checkSCC(varIdx, valIdx)) {
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
        for (int i = nextSetBit(graphLinkedFrontier[varIdx], 0);
             i != BITS_PER_WORD; i = nextSetBit(graphLinkedFrontier[varIdx], 0)) {
            graphLinkedFrontier[varIdx] |= graphLinkedMatrix[i] & ~graphLinkedMatrix[varIdx];
            graphLinkedFrontier[varIdx] &= ~(1L << i);
            graphLinkedMatrix[varIdx] |= graphLinkedMatrix[i];
            if ((graphLinkedMatrix[varIdx] & 1L << val2Var[valIdx]) != 0L) {
                return true;
            }
        }
        return false;
    }

    private int nextSetBit(long word, int pos) {
        return Long.numberOfTrailingZeros(word & -1L << pos);
    }

}