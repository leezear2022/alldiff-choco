package org.chocosolver.solver.constraints.nary.alldifferent.algo;

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
import org.chocosolver.util.graphOperations.connectivity.StrongConnectivityFinderR3;
import org.chocosolver.util.objects.IntTuple2;
import org.chocosolver.util.objects.Measurer;
import org.chocosolver.util.objects.RSetPartition;
import org.chocosolver.util.objects.SparseSet;
import org.chocosolver.util.objects.graphs.DirectedGraph;
import org.chocosolver.util.objects.setDataStructures.SetType;
import org.chocosolver.util.procedure.UnaryIntProcedure;

import java.util.ArrayList;
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
public class AlgoAllDiffAC_Gent20 {

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

//    // 值编号对应的变量（不包括匹配变量）
//    private SparseSet[] valUnmatchedVar;

    // 自由值集合
//    private SparseSet freeNode;

    // 新增一点（视为变量）
    private int addArity;

    //    // SCC
    private int numNodes;

    private DirectedGraph graph;
    private int[] node2SCC;
    private TIntArrayList[] SCC2Node;
    //    private StrongConnectivityNewFinder SCCfinder;
    private StrongConnectivityFinderR3 SCCfinder;
//    private StrongConnectivityFinder SCCfinder;

    // for early detection
    protected IIntDeltaMonitor[] monitors;
    private UnaryIntProcedure<Integer> onValRem;
    private TLongArrayStack DE;
    private boolean initialProp = true;

    private SparseSet triggeringVars;
    private TIntHashSet SCCStartIndex;
    private TIntHashSet changedSCCStartIndex;
    private RSetPartition partition;

    //    //    //用于回溯
//    private IStateBitSet[] RDbit, RBbit;
//
//    //    // 与值相连的变量
//    private INaiveBitSet[] Bbit;
//    //    // bit论域
//    private INaiveBitSet[] Dbit;
//    private INaiveBitSet[] lastDbit;
//    private INaiveBitSet varsMask;
//    private ArrayList<IntTuple2> delValues1;
//    private ArrayList<IntTuple2> addValues;
//    private ArrayList<IntTuple2> delValues2;
    IEnvironment env;
    private TIntArrayList[] deletedValues;

//    private int numNodes;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_Gent20(IntVar[] variables, ICause cause, Model model) {
        id = num++;
        env = model.getEnvironment();

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

//        valUnmatchedVar = new SparseSet[numValues];
//        for (int i = 0; i < numValues; ++i) {
//            valUnmatchedVar[i] = new SparseSet(addArity);
//        }

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

        // freeNode区分匹配点和非匹配点(正好是新增变量的取值范围）
//        freeNode = new SparseSet(numValues);

        // SCC
        numNodes = addArity + numValues;

        graph = new DirectedGraph(numNodes, SetType.BITSET, false);
//        SCCfinder = new StrongConnectivityNewFinder(graph);
//        SCCfinder = new StrongConnectivityFinderR(graph);
        partition = new RSetPartition(numNodes, env);
//        System.out.println(partition);
        SCCfinder = new StrongConnectivityFinderR3(graph, arity, numValues, partition, id);
        numNodes = graph.getNbMaxNodes();
        node2SCC = new int[numNodes];
        SCC2Node = new TIntArrayList[numNodes];
        for (int i = 0; i < numNodes; i++) {
            SCC2Node[i] = new TIntArrayList();
        }
//        SCCfinder = new StrongConnectivityFinder(graph);

        //for early detection
        // 存的是变量索引及原值
//        DE = new Stack<IntTuple2>();
        DE = new TLongArrayStack();
//        SCCfinder = new StrongConnectivityNewFinder(digraph, DE);
        deletedValues = new TIntArrayList[arity];
        for (int i = 0; i < arity; i++) {
            deletedValues[i] = new TIntArrayList(numValues);
        }

        // for delta
        monitors = new IIntDeltaMonitor[vars.length];
        for (int i = 0; i < vars.length; i++) {
            monitors[i] = vars[i].monitorDelta(cause);
        }
        onValRem = makeProcedure();

        //for early detection
        // 存的是变量索引及原值
//        DE = new Stack<IntTuple2>();
        triggeringVars = new SparseSet(arity);
        SCCStartIndex = new TIntHashSet();
        changedSCCStartIndex = new TIntHashSet();

//        // 两种记录已删除的值
//        delValues1 = new ArrayList<>();
//        delValues2 = new ArrayList<>();
//        addValues = new ArrayList<>();
//
//        Bbit = new INaiveBitSet[numValues];
//        RBbit = new IStateBitSet[numValues];
//        for (int i = 0; i < numValues; ++i) {
//            Bbit[i] = INaiveBitSet.makeBitSet(arity, false);
//            RBbit[i] = env.makeBitSet(arity);
//        }
//
//        Dbit = new INaiveBitSet[arity];
//        lastDbit = new INaiveBitSet[arity];
//        RDbit = new IStateBitSet[arity];
//        int valSize = val2Idx.size();
//        for (int i = 0; i < arity; i++) {
//            Dbit[i] = INaiveBitSet.makeBitSet(valSize, false);
//            lastDbit[i] = INaiveBitSet.makeBitSet(valSize, false);
//            RDbit[i] = env.makeBitSet(valSize);
//        }
//
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
//                int valIdx = val2Idx.get(j);
//                Bbit[valIdx].set(i);
//                RBbit[valIdx].set(i);
//                Dbit[i].set(valIdx);
//                lastDbit[i].set(valIdx);
//                RDbit[i].set(valIdx);
//            }
//        }
//
//        varsMask = INaiveBitSet.makeBitSet(arity, true);
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
                return this;
            }

            @Override

            public void execute(int i) throws ContradictionException {
                if (!triggeringVars.contains(var)) {
                    triggeringVars.add(var);
                    deletedValues[var].clear();
                }

                deletedValues[var].add(val2Idx.get(i) + addArity);
            }
        };
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    public boolean propagate() throws ContradictionException {
//        System.out.println("---------------");
//        System.out.println("propagate cid: " + id);
        boolean filter = false;
        long startTime;
        triggeringVars.clear();

        if (initialProp) {
            initialProp = false;

            for (int i = 0; i < arity; i++) {
                triggeringVars.add(i);
            }

            startTime = System.nanoTime();
            Measurer.enterProp();
            prepareForMatching();
            findMaximumMatching();
            Measurer.matchingTime += System.nanoTime() - startTime;

            startTime = System.nanoTime();
            filter = filter();
            Measurer.filterTime += System.nanoTime() - startTime;

            return filter;
        } else {
            Measurer.enterProp();
            startTime = System.nanoTime();
//            DE.clear();
//            triggeringVars.clear();
            for (int i = 0; i < arity; ++i) {
                monitors[i].freeze();
                monitors[i].forEachRemVal(onValRem.set(i));
            }

//            SCCfinder.getAllSCCStartIndices(SCCStartIndex);
//            System.out.println("triggeringVars: " + triggeringVars);
//            System.out.println(partition);
            prepareForMatching();
            filter |= propagate_SCC_Match();
            Measurer.matchingTime += System.nanoTime() - startTime;

            startTime = System.nanoTime();
            filter |= propagate_SCC_filter();
            for (int i = 0; i < vars.length; i++) {
                monitors[i].unfreeze();
            }
            Measurer.filterTime += System.nanoTime() - startTime;

            return filter;
        }
    }

    private void printValues(ArrayList<IntTuple2> values) {
        for (var a : values) {
            System.out.print(a + ", ");
        }
        System.out.println();
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

            if (x.isInstantiated()&& partition.greatThanOne(sccStartIdx)) {
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
//                            System.out.println("remove: " + yIdx + "," + xVal);
//                            Dbit[yIdx].clear(val2Idx.get(xVal));
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

    private boolean propagate_SCC_filter() throws ContradictionException {
        buildGraph();
//        SCCfinder.setUnvisitedValues();
        SCCfinder.resetData_ED();
        boolean isSkip = true;
        var iter = changedSCCStartIndex.iterator();

        while (iter.hasNext()) {
            DE.clear();
            int sccStartIndex = iter.next();
            partition.setIteratorIndex(sccStartIndex);
            do {
                int varIdx = partition.getValue();
                if (varIdx < arity && triggeringVars.contains(varIdx)) {
                    var valIter = deletedValues[varIdx].iterator();
                    while ((valIter.hasNext())) {
                        DE.push(SCCfinder.getIntTuple2Long(varIdx, valIter.next()));
                    }
                }
            } while (partition.nextValid());

            boolean res = SCCfinder.findAllSCC_ED(sccStartIndex, DE);
            isSkip = res && isSkip;
        }

        // isSkip全是true才ED有不是true的表明删值了
        if (isSkip) {
            Measurer.enterSkip();
            return true;
        }

        boolean filter = filterDomains();
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

            //? 可在一个scc中选择值
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

//                    freeNode.remove(valIdx);
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
//                    freeNode.remove(valIdx);
                }
            }
        }
    }

    private void prepareForMatching() {
//        freeNode.fill();
        // 增量检查
        // matching 有效性检查
        triggeringVars.iterateValid();
        while (triggeringVars.hasNextValid()) {
            int varIdx = triggeringVars.next();
            IntVar v = vars[varIdx];
            if (v.getDomainSize() == 1) {
                // 取出变量的唯一值
                int valIdx = val2Idx.get(v.getValue());
//                valUnmatchedVar[valIdx].add(varIdx);
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
//                freeNode.remove(valIdx);
            } else {
                // 检查原匹配是否失效
                int oldMatchingIndex = var2Val[varIdx];
                if (oldMatchingIndex != -1) {
                    // 如果oldMatchingValue无效
                    if (!v.contains(idx2Val[oldMatchingIndex])) {
                        val2Var[oldMatchingIndex] = -1;
                        var2Val[varIdx] = -1;
                    } else {
//                        freeNode.remove(oldMatchingIndex);
//                    System.out.println(oldMatchingIndex + " is free");
                    }
                }
            }
        }
    }

    private void repairMatching(int SCCStartIndex) throws ContradictionException {
        // repair max matching.
        partition.setIteratorIndex(SCCStartIndex);
        do {
            int varIdx = partition.getValue();
            if (varIdx < arity) {
                if (var2Val[varIdx] == -1) {
                    value_visited_.clear();
                    variable_visited_.clear();
                    MakeAugmentingPath(varIdx);
                }

                if (var2Val[varIdx] == -1) {
                    for (int i = 0; i < vars.length; i++) {
                        monitors[i].unfreeze();
                    }

                    vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
                }
            }
        } while (partition.nextValid());
    }

    private void findMaximumMatching() throws ContradictionException {
        // Compute max matching.
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            if (var2Val[varIdx] == -1) {
                value_visited_.clear();
                variable_visited_.clear();
                MakeAugmentingPath(varIdx);
            }
            if (var2Val[varIdx] == -1) {
                // No augmenting path exists.
                for (int i = 0; i < vars.length; i++) {
                    monitors[i].unfreeze();
                }
                vars[0].instantiateTo(vars[0].getLB() - 1, aCause);
            }
        }
    }

    //***********************************************************************************
    // PRUNING
    //***********************************************************************************

    private void buildGraph() {
        for (int i = 0; i < numNodes; i++) {
            graph.getSuccOf(i).clear();
            graph.getPredOf(i).clear();
        }

        // 反向边
        for (int i = 0; i < arity; ++i) {
            int matchedVal = var2Val[i];
            IntVar v = vars[i];

            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
                int valIdx = val2Idx.get(j);
                if (valIdx == matchedVal) {
                    // 添加匹配边 var<--val
                    graph.addArc(valIdx + addArity, i);
//                    System.out.printf("添加匹配边 %d->%d\n", valIdx + addArity, i);
                } else {
                    // 添加非匹配边 var-->val
                    graph.addArc(i, valIdx + addArity);
//                    System.out.printf("添加非匹配边 %d->%d\n", i, valIdx + addArity);
                }

                // 值的匹配变量=-1表明它是freenode
                if (val2Var[valIdx] == -1) {
                    // free node: val->t
                    graph.addArc(valIdx + addArity, arity);
//                    System.out.printf("free node: %d->%d\n", j + addArity, arity);
                } else {
                    // matched node: t->val;
                    graph.addArc(arity, valIdx + addArity);
//                    System.out.printf("matched node: %d->%d\n", arity, valIdx + addArity);
                }
            }
        }
    }

    private void buildSCC() {
        //新buildGraph
        buildGraph();

        SCCfinder.getAllSCCStartIndices(SCCStartIndex);
//        System.out.println(partition);
//        System.out.println("indices: " + SCCStartIndex);
        SCCfinder.resetData();
        TIntIterator iter = SCCStartIndex.iterator();
        while (iter.hasNext()) {
            SCCfinder.findAllSCC(iter.next());
//            System.out.println("------");
        }
//        SCCfinder.findAllSCC();
//        SCCfinder.findAllSCC(0);
//        node2SCC = SCCfinder.getNodesSCC();
//        SCCfinder.getNodesSCC(node2SCC, SCC2Node);

//        System.out.println(Arrays.toString(node2SCC));
//        System.out.println(partition);
//        SCCfinder.getAllSCCStartIndices(SCCStartIndex);
//        System.out.println("indices: " + SCCStartIndex);
//        graph.removeNode(numNodes);
    }

    private boolean filter() throws ContradictionException {
        buildSCC();
        return filterDomains();
    }

    private boolean filterDomains() throws ContradictionException {
        boolean filter = false;
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            IntVar v = vars[varIdx];
            if (!v.isInstantiated()) {
                int ub = v.getUB();
                for (int k = v.getLB(); k <= ub; k = v.nextValue(k)) {
                    int valIdx = val2Idx.get(k);
//                    if (node2SCC[varIdx] != node2SCC[valIdx + addArity]) {
                    if (!partition.inSameSCC(varIdx, valIdx + addArity)) {
                        Measurer.enterP2();
                        if (valIdx == var2Val[varIdx]) {
                            int valNum = v.getDomainSize();
                            Measurer.numDelValuesP2 += valNum - 1;
//                            System.out.println("instantiate  : " + v.getName() + ", " + k + " P2: " + Measurer.numDelValuesP2);
//                            RDbit[varIdx].clear();
//                            RDbit[varIdx].set(valIdx);
//                            Dbit[varIdx].clear();
//                            Dbit[varIdx].set(valIdx);
                            filter |= v.instantiateTo(k, aCause);
                        } else {
                            ++Measurer.numDelValuesP2;
//                            System.out.println("second delete: " + v.getName() + ", " + k + " P2: " + Measurer.numDelValuesP2);
//                            RDbit[varIdx].clear(valIdx);
//                            Dbit[varIdx].clear(valIdx);
                            filter |= v.removeValue(k, aCause);
                        }
                    }
                }
            }
        }
        return filter;
    }


}