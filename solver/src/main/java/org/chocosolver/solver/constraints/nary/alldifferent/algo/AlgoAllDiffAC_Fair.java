package org.chocosolver.solver.constraints.nary.alldifferent.algo;

//import org.chocosolver.amtf.Measurer;

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.map.hash.TIntIntHashMap;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.graphOperations.connectivity.StrongConnectivityFinderR;
import org.chocosolver.util.objects.Measurer;
import org.chocosolver.util.objects.SparseSet;
import org.chocosolver.util.objects.graphs.DirectedGraph;
import org.chocosolver.util.objects.setDataStructures.SetType;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;

/**
 * Algorithm of Alldifferent with AC
 * <p>
 * Uses Regin algorithm with FF-BFS incremental matching + graph based scc
 * Runs in O(m.n) worst case time for the initial propagation
 * but has a good average behavior in practice
 * <p/>
 * Keeps track of previous matching for further calls
 * <p/>
 *
 * @author Jean-Guillaume Fages
 */
public class AlgoAllDiffAC_Fair {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************
    // 约束的个数
    static public int num = 0;
    // 约束的编号
    private int id;
    //for debug
    static private long numCall = -1;

    private int arity;
    private IntVar[] vars;
    private ICause aCause;

    // numValue是二部图中取值编号的个数
    private int numValues;

    // 索引到值
    private int[] idx2Val;
    // 值到索引
    private TIntIntHashMap val2Idx;

    // 已访问过的变量和值
    private BitSet variable_visited_;
    private BitSet value_visited_;

    // matching
    private int[] val2Var;
    private int[] var2Val;

    // 记录队列
    private int[] visiting_;
    private int[] variable_visited_from_;

    // 值编号对应的变量（不包括匹配变量）
    private SparseSet[] valUnmatchedVar;

    // 自由值集合
    private SparseSet freeNode;

    // 新增一点（视为变量）
    private int addArity;

    //    // SCC
    private int numNodes;

    private DirectedGraph graph;
    private int[] nodeSCC;
    private StrongConnectivityFinderR SCCfinder;
    private long startTime;


    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_Fair(IntVar[] variables, ICause cause) {
        id = num++;

        this.vars = variables;
        aCause = cause;
        arity = vars.length;
        addArity = arity + 1;
        val2Idx = new TIntIntHashMap();
        // 统计所有变量论域中不同值的个数
        for (int i = 0; i < arity; ++i) {
            IntVar v = vars[i];
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

        // 记录访问过的变量
        visiting_ = new int[arity];
        variable_visited_ = new BitSet(arity);
        // 变量的前驱变量，若前驱变量是-1，则表示无前驱变量，就是第一个变量
        variable_visited_from_ = new int[arity];
        value_visited_ = new BitSet(numValues);

        var2Val = new int[arity];
        for (int i = 0; i < arity; ++i) {
            var2Val[i] = -1;
        }
        val2Var = new int[numValues];
        for (int i = 0; i < numValues; ++i) {
            val2Var[i] = -1;
        }

        valUnmatchedVar = new SparseSet[numValues];
        for (int i = 0; i < numValues; ++i) {
            valUnmatchedVar[i] = new SparseSet(arity);
        }
        // freeNode区分匹配点和非匹配点(正好是新增变量的取值范围）
        freeNode = new SparseSet(numValues);

        // SCC
        numNodes = addArity + numValues;
        nodeSCC = new int[numNodes];

        graph = new DirectedGraph(numNodes, SetType.BITSET, false);
        SCCfinder = new StrongConnectivityFinderR(graph, id);
        SCCfinder.setArity(arity);
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************
    void printDomains() {
//        for (var v : vars) {
//            System.out.print(v.getId() + "\t\t: ");
//            for (int k = v.getLB(), ub = v.getUB(); k <= ub; k = v.nextValue(k)) {
//                System.out.print(k + " ");
//            }
//            System.out.println();
//        }
        // 填充B和D
        for (var v : vars) {
            System.out.println(v);
        }
    }

    public boolean propagate() throws ContradictionException {
//        System.out.println(" propagate: " + (++numCall) + "----------------");
//        printDomains();
        Measurer.enterProp();
//        if (id == 30 && numCall == 68) {
//            System.out.println("before repair: " + Arrays.toString(var2Val));
//            System.out.println(Arrays.toString(nodeSCC));
//        }
        startTime = System.nanoTime();
        findMaximumMatching();
        Measurer.matchingTime += System.nanoTime() - startTime;
//        System.out.println("matching: "+ Arrays.toString(var2Val));
//        if (id == 30 && numCall == 68)
//            System.out.println("after repair: " + Arrays.toString(var2Val));
////        System.out.println("-----final matching-----");
//        for (int i = 0; i < arity; i++) {
//            System.out.println(vars[i].getName() + " match " + idx2Val[var2Val[i]]);
//        }
////        System.out.println("------------------");

//        if (id == 7) {
//            System.out.println(Arrays.toString(var2Val));
//        }

        startTime = System.nanoTime();
        boolean filter = filter();
        Measurer.filterTime += System.nanoTime() - startTime;
//        printDomains();
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
        variable_visited_.set(start);
        variable_visited_from_[start] = -1;

        while (num_visited < num_to_visit) {
            // Dequeue node to visit.
            int node = visiting_[num_visited++];
            IntVar v = vars[node];

            for (int value = v.getLB(), ub = v.getUB(); value <= ub; value = v.nextValue(value)) {

                int valIdx = val2Idx.get(value);
                if (value_visited_.get(valIdx)) continue;
//                xixi++;
                value_visited_.set(valIdx);
//                System.out.println(xixi + ", " + node + ", " + valIdx);
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
                    freeNode.remove(valIdx);
                }
            }
        }
    }

    private void findMaximumMatching() throws ContradictionException {
        for (int i = 0; i < numValues; ++i) {
            valUnmatchedVar[i].clear();
//            valUnmatchedVar[i].add(arity);
        }
        freeNode.fill();
        // 增量检查
        // matching 有效性检查
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            IntVar v = vars[varIdx];
            if (v.getDomainSize() == 1) {
                // 取出变量的唯一值
                int valIdx = val2Idx.get(v.getValue());
                valUnmatchedVar[valIdx].add(varIdx);
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
//                    System.out.println(oldMatchingIndex + " is free");
                    }
                }

                for (int value = v.getLB(), ub = v.getUB(); value <= ub; value = v.nextValue(value)) {
                    int valIdx = val2Idx.get(value);
                    // Forward-checking should propagate xsu != value.
                    valUnmatchedVar[valIdx].add(varIdx);
                }
            }
        }

//        if (id == 7) {
//            System.out.println(Arrays.toString(var2Val));
//        }

        // Compute max matching.
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            if (var2Val[varIdx] == -1) {
                value_visited_.clear();
                variable_visited_.clear();
                MakeAugmentingPath(varIdx);
            }
            if (var2Val[varIdx] == -1) {
                // No augmenting path exists.
//                System.out.println("match fail");
                Measurer.matchingTime += System.nanoTime() - startTime;
                vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
            }
        }

        for (int varIdx = 0; varIdx < arity; varIdx++) {
            valUnmatchedVar[var2Val[varIdx]].remove(varIdx);
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

    private void buildSCC() {

        for (int i = 0; i < numNodes; i++) {
            graph.getSuccOf(i).clear();
            graph.getPredOf(i).clear();
        }

        // 反向边
        // 添加匹配边 var<--val
        for (int i = 0; i < arity; ++i) {
            int matchedVal = var2Val[i];
            graph.addArc(matchedVal + addArity, i);

        }

        // 添加非匹配边 val<--var; val<--t
        for (int j = 0, k = 0; j < numValues; ++j) {
            if (freeNode.contains(j)) {
                // free node: val->t
                graph.addArc(j + addArity, arity);
            } else {
                // free node: t->val;
                graph.addArc(arity, j + addArity);
            }
            valUnmatchedVar[j].iterateValid();
            while (valUnmatchedVar[j].hasNextValid()) {
                k = valUnmatchedVar[j].next();
                graph.addArc(k, j + addArity);
            }
        }
//        if (id == 30 && numCall == 68){
//            System.out.println("xixi");
//        }

        SCCfinder.findAllSCC();
        nodeSCC = SCCfinder.getNodesSCC();

//        if (id == 30 && numCall == 68) {
//            printDoms();
//            System.out.println(Arrays.toString(var2Val));
//            System.out.println(graph);
//            System.out.println(Arrays.toString(nodeSCC));
//        }
//        System.out.println(Arrays.toString(nodeSCC));
    }

    private boolean filter() throws ContradictionException {
        boolean filter = false;
        buildSCC();
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            IntVar v = vars[varIdx];
            if (!v.isInstantiated()) {
                int ub = v.getUB();
                for (int k = v.getLB(); k <= ub; k = v.nextValue(k)) {
                    int valIdx = val2Idx.get(k);
                    if (nodeSCC[varIdx] != nodeSCC[valIdx + addArity]) {
                        Measurer.enterP2();
                        if (valIdx == var2Val[varIdx]) {
                            int valNum = v.getDomainSize();
                            Measurer.numDelValuesP2 += valNum - 1;
//                            if (id == 30 && numCall == 68)
//                            System.out.println("instantiate:\t" + varIdx + ", " + valIdx);
                            filter |= v.instantiateTo(k, aCause);
                        } else {
                            ++Measurer.numDelValuesP2;
//                            if (id == 30 && numCall == 68)
//                            System.out.println("second delete:\t" + varIdx + ", " + valIdx);
                            filter |= v.removeValue(k, aCause);
                        }
                    }
                }
            }
        }

//        if (id == 30 && numCall == 68){
//            printDoms();
//            System.out.println("final: " + filter);
//        }
        return filter;
    }
}