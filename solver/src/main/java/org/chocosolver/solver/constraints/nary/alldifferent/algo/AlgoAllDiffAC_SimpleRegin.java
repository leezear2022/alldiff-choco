package org.chocosolver.solver.constraints.nary.alldifferent.algo;

//import org.chocosolver.amtf.Measurer;

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.map.hash.TIntIntHashMap;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.Measurer;
import org.chocosolver.util.objects.SimpleBitSet;
import org.chocosolver.util.objects.SparseSet;

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
public class AlgoAllDiffAC_SimpleRegin extends AlgoAllDiffAC_Simple {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************
    // 约束的个数
//    static public int num = 0;
    // 约束的编号
    static long numCall = -1;
    static private int num = 0;
    // 自由值集合
    private SparseSet freeNode;
    private SimpleBitSet freeNodes;

    // 以下是bit版本所需数据结构========================
    // numValues是二部图中取值编号的个数，numBit是二部图的最大边数
//    private int numValues;
    // 值到索引
//    private int[] idx2Val;
    // 索引到值
//    private TIntIntHashMap val2Idx;

    // Xc-Γ(A)
    private SparseSet notGamma;
    // Dc-A
    private SparseSet notA;

    // 与值相连的变量
    private SimpleBitSet[] valMask;

    // 已访问过的变量和值
    private SimpleBitSet variable_visited_;
    private SimpleBitSet value_visited_;

    // matching
    private int[] val2Var;
    private int[] var2Val;

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

    long startTime;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_SimpleRegin(IntVar[] variables, ICause cause) {
        super(variables, cause);
        id = num++;
//        System.out.println("-----------idx2Val-----------");
//        System.out.println(Arrays.toString(idx2Val));

        valMask = new SimpleBitSet[numValues];
        for (int i = 0; i < numValues; ++i) {
            valMask[i] = new SimpleBitSet(arity);
        }

        // 记录访问过的变量
        visiting_ = new int[arity];
        variable_visited_ = new SimpleBitSet(arity);
        // 变量的前驱变量，若前驱变量是-1，则表示无前驱变量，就是第一个变量
        variable_visited_from_ = new int[arity];
        value_visited_ = new SimpleBitSet(numValues);

        var2Val = new int[arity];
        val2Var = new int[numValues];
        for (int i = 0; i < arity; ++i) {
            var2Val[i] = -1;
        }
        for (int i = 0; i < numValues; ++i) {
            val2Var[i] = -1;
        }

        freeNode = new SparseSet(numValues);
        freeNodes = new SimpleBitSet(numValues);
        gammaFrontier = new SimpleBitSet(arity);
        gammaMask = new SimpleBitSet(arity);
        notGamma = new SparseSet(arity);
        notA = new SparseSet(numValues);

        graphLinkedMatrix = new SimpleBitSet[arity];
        graphLinkedFrontier = new SimpleBitSet[arity];
        for (int i = 0; i < arity; ++i) {
            graphLinkedMatrix[i] = new SimpleBitSet(arity);
            graphLinkedFrontier[i] = new SimpleBitSet(arity);
        }
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    public boolean propagate() throws ContradictionException {
        System.out.println("----------------" + id + " propagate: " + (++numCall) + "----------------");
        printDomains();
        Measurer.enterProp();
        startTime = System.nanoTime();
        findMaximumMatching();
        Measurer.matchingTime += System.nanoTime() - startTime;
        System.out.println("matching: " + Arrays.toString(var2Val));
        startTime = System.nanoTime();

        boolean filter = filter();
        Measurer.filterTime += System.nanoTime() - startTime;
        if (numCall == 683) {
            printDomains();
        }
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

                    freeNodes.clear(valIdx);
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
                    freeNodes.clear(valIdx);
                    freeNode.remove(valIdx);
                }
            }
        }
    }

    private void findMaximumMatching() throws ContradictionException {
        // !! 可做增量
        for (int i = 0; i < numValues; ++i) {
            valMask[i].clear();
        }

        freeNodes.set();
        freeNode.fill();

        // 增量检查
        // matching 有效性检查
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            IntVar v = vars[varIdx];
            // !! 这里可以修改一下 已赋值 就不参与修改了
            if (v.getDomainSize() == 1) {
                // 取出变量的唯一值
                int valIdx = val2Idx.get(v.getValue());
                valMask[valIdx].set(varIdx);
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
                freeNodes.clear(valIdx);
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
                        freeNodes.clear(oldMatchingIndex);
                        freeNode.remove(oldMatchingIndex);
//                    System.out.println(oldMatchingIndex + " is free");
                    }
                }

                for (int value = v.getLB(), ub = v.getUB(); value <= ub; value = v.nextValue(value)) {
                    int valIdx = val2Idx.get(value);
                    // Forward-checking should propagate xsu != value.
                    // !! 可以增量修改值
                    valMask[valIdx].set(varIdx);
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
                Measurer.matchingTime += System.nanoTime() - startTime;
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

//        freeNode.iterateValid();
//        while (freeNode.hasNextValid()) {
        for (int valIdx = freeNodes.nextSetBit(0);
             valIdx >= 0; valIdx = freeNodes.nextSetBit(valIdx + 1)) {
            // 每个freeNode的值拿出来
//            System.out.println(i);
//            int valIdx = freeNode.next();
            notA.remove(valIdx);
            gammaMask.or(valMask[valIdx]);
//            if (numCall == 2) {
//                System.out.println("add " + valIdx + ": " + gammaMask);
//            }
        }
        gammaFrontier.set(gammaMask);

        for (int varIdx = gammaFrontier.nextSetBit(0);
             varIdx != -1; varIdx = gammaFrontier.nextSetBit(0)) {
            // !! 这里可以将Extended改成Frontier，只记录前沿，记录方法是三个BitSet比较，
            // frontier 扩展，从valMask中去掉gammaMask已记录的变量
            int valIdx = var2Val[varIdx];
            gammaFrontier.orAfterMinus(valMask[valIdx], gammaMask);
//            // 除去第i个变量
            gammaFrontier.clear(varIdx);
            // gamma 扩展
            gammaMask.or(valMask[valIdx]);
//            freeNodes.set(valIdx);

            notGamma.remove(varIdx);
            notA.remove(valIdx);
        }

    }

    private void initiateMatrix() {
        // 重置两个矩阵
        // 只重置notGamma的变量
        System.out.println("gamma: " + gammaMask);
        notGamma.iterateValid();
        while (notGamma.hasNextValid()) {
            int varIdx = notGamma.next();
            // 从变量id拿到匹配值再拿到该值所能到达的变量mask
            if (!vars[varIdx].isInstantiated()) {
                graphLinkedMatrix[varIdx].setAfterMinus(valMask[var2Val[varIdx]], gammaMask);
                graphLinkedMatrix[varIdx].clear(varIdx);
                graphLinkedFrontier[varIdx].set(graphLinkedMatrix[varIdx]);

//                if (numCall == 106) {
//                    System.out.println("------graphLinkedMatrix[" + varIdx + "]------");
//                    System.out.println(graphLinkedMatrix[varIdx]);
//                    System.out.println(graphLinkedFrontier[varIdx]);
//                }
            }
        }
    }

    private boolean filter() throws ContradictionException {
        System.out.println("freeNodes: " + freeNodes);
        distinguish();
        initiateMatrix();
        // 这里判断一下，如果notGamma为空则不用进行如下步骤
        boolean filter = false;
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            IntVar v = vars[varIdx];
            if (!v.isInstantiated()) {
                for (int k = v.getLB(), ub = v.getUB(); k <= ub; k = v.nextValue(k)) {
                    int valIdx = val2Idx.get(k);
                    if (!notGamma.contains(varIdx) && notA.contains(valIdx)) {
                        ++Measurer.numDelValuesP1;
                        Measurer.enterP1();
                        filter |= v.removeValue(k, aCause);
                        System.out.println("first delete: " + varIdx + ", " + valIdx);
                    } else if (notGamma.contains(varIdx) && notA.contains(valIdx)) {
                        if (!checkSCC(varIdx, valIdx)) {
                            Measurer.enterP2();
                            if (varIdx == val2Var[valIdx]) {
                                int valNum = v.getDomainSize();
                                Measurer.numDelValuesP2 += valNum - 1;
                                filter |= v.instantiateTo(k, aCause);
                                System.out.println("instantiate  : " + varIdx + ", " + valIdx);
                            } else {
                                ++Measurer.numDelValuesP2;
                                filter |= v.removeValue(k, aCause);
                                System.out.println("second delete: " + varIdx + ", " + valIdx);
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
        if (graphLinkedMatrix[varIdx].get(val2Var[valIdx])) {
            return true;
        }
        for (int i = graphLinkedFrontier[varIdx].nextSetBit(0);
             i != -1; i = graphLinkedFrontier[varIdx].nextSetBit(0)) {
            // frontier扩张，除掉变量i 因为变量i已被扩展。
            // frontier扩
            graphLinkedFrontier[varIdx].orAfterMinus(graphLinkedMatrix[i], graphLinkedMatrix[varIdx]);
            graphLinkedFrontier[varIdx].clear(i);
            graphLinkedMatrix[varIdx].or(graphLinkedMatrix[i]);
            if (graphLinkedMatrix[varIdx].get(val2Var[valIdx])) {
                return true;
            }
        }
        return false;
    }


    private void printDomains() {


        // 填充B和D
        for (int i = 0; i < arity; ++i) {
            IntVar v = vars[i];
            System.out.println(v);
        }
    }
    @Override
    protected void removeValueR(int varIdx, int valIdx) {
    }

    @Override
    protected void instantiateToR(int varIdx, int valIdx) {
    }

//    private void printBitDomains() {
//        for (int i = 0; i < numValuess; ++i) {
//            System.out.println("val " + "i: " + B[i]);
//        }
//
//        IntVar v;
//        // 填充B和D
//        for (int i = 0; i < arity; ++i) {
//            v = vars[i];
//            System.out.println("val " + "i: " + D[i]);
//            System.out.println(v);
//        }
//    }

}