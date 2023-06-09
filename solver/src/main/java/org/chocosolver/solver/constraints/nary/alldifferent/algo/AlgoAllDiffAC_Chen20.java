package org.chocosolver.solver.constraints.nary.alldifferent.algo;

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.map.hash.TIntIntHashMap;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.delta.IIntDeltaMonitor;
import org.chocosolver.util.objects.IntPair;
import org.chocosolver.util.objects.Measurer;
import org.chocosolver.util.objects.SparseSet;
import org.chocosolver.util.procedure.UnaryIntProcedure;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Stack;

/**
 * Algorithm of Alldifferent with AC
 * <p>
 * Uses Regin algorithm
 * Runs in O(m.n) worst case time for the initial propagation
 * but has a good average behavior in practice
 * <p/>
 * Keeps track of previous matching for further calls
 * <p/>
 *
 * @author Jean-Guillaume Fages
 */
public class AlgoAllDiffAC_Chen20 {

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
    private int numValue;

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

    // SCC
    private int n, nbSCC, stackIdx, searchIdx;
    private int[] nodeSCC;

    // util
    private int[] stack, p, inf, dfn;
    private BitSet inStack, unvisited;

    // for early detection
    protected IIntDeltaMonitor[] monitors;
    private UnaryIntProcedure<Integer> onValRem;
    private Stack<IntPair> DE;
    private boolean initialProp = true;
    private boolean unconnected = false;
    private ArrayList<IntPair> cycles;
    private IntPair tt;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_Chen20(IntVar[] variables, ICause cause) {
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

        numValue = val2Idx.size();
        idx2Val = new int[numValue];
        TIntIntIterator it = val2Idx.iterator();
        while (it.hasNext()) {
            it.advance();
            idx2Val[it.value()] = it.key();
        }

        valUnmatchedVar = new SparseSet[numValue];
        for (int i = 0; i < numValue; ++i) {
            valUnmatchedVar[i] = new SparseSet(addArity);
        }

        // 记录访问过的变量
        visiting_ = new int[arity];
        variable_visited_ = new BitSet(arity);
        // 变量的前驱变量，若前驱变量是-1，则表示无前驱变量，就是第一个变量
        variable_visited_from_ = new int[arity];
        value_visited_ = new BitSet(numValue);

        var2Val = new int[arity];
        for (int i = 0; i < arity; ++i) {
            var2Val[i] = -1;
        }
        val2Var = new int[numValue];
        for (int i = 0; i < numValue; ++i) {
            val2Var[i] = -1;
        }

        // freeNode区分匹配点和非匹配点(正好是新增变量的取值范围）
        freeNode = new SparseSet(numValue);

        // SCC
        n = addArity + numValue;
        nodeSCC = new int[n];

        stack = new int[n];
        p = new int[n];
        inf = new int[n];
        dfn = new int[n];
        inStack = new BitSet(n);
        unvisited = new BitSet(addArity);

        //for early detection
        // 存的是变量索引及原值
        DE = new Stack<>();
        cycles = new ArrayList<>();
//        SCCfinder = new StrongConnectivityNewFinder(digraph, DE);

        // for delta
        monitors = new IIntDeltaMonitor[vars.length];
        for (int i = 0; i < vars.length; i++) {
            monitors[i] = vars[i].monitorDelta(cause);
        }
        onValRem = makeProcedure();
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
                DE.push(new IntPair(var, val2Idx.get(i) + addArity));
//                IntVar v = vars[var];
//                System.out.println(vars[var].getName() + "," + var + ", " + i + " = " + v.contains(i) + ", size = " + v.getDomainSize());
            }
        };
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    public boolean propagate() throws ContradictionException {
//        System.out.println("----------------" + id + " propagate----------------");
//        if (id == 0) {
//            System.out.println("vars: ");
//            for (IntVar v : vars) {
//                System.out.println(v.toString());
//            }
//        }
        Measurer.enterProp();
        long startTime = System.nanoTime();
        DE.clear();
        for (int i = 0; i < arity; ++i) {
            monitors[i].freeze();
            monitors[i].forEachRemVal(onValRem.set(i));
        }
//        System.out.println("DE: " + DE);
        findMaximumMatching();
        Measurer.matchingTime += System.nanoTime() - startTime;

        startTime = System.nanoTime();
        boolean filter = filter();
        for (int i = 0; i < vars.length; i++) {
            monitors[i].unfreeze();
        }
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
        for (int i = 0; i < numValue; ++i) {
            valUnmatchedVar[i].clear();
            valUnmatchedVar[i].add(arity);
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

        for (int varIdx = 0; varIdx < arity; varIdx++) {
            valUnmatchedVar[var2Val[varIdx]].remove(varIdx);
        }

//        if (id == 2) {
//        System.out.println("-----final matching-----");
//        for (int i = 0; i < arity; i++) {
//            System.out.println(vars[i].getName() + " match " + idx2Val[var2Val[i]]);
//        }
//        System.out.println("------------------");
//        }
//        System.out.println(Arrays.toString(var2Val));
//        System.out.println(Arrays.toString(val2Var));
//        System.out.println(freeNode);
    }

    //***********************************************************************************
    // PRUNING
    //***********************************************************************************

    private boolean buildSCC() {
        // 初始化
        // restriction记录寻找SCC的过程中未访问的变量
//        restriction.clear();
//        restriction.flip(0, addArity);
        unvisited.set(0, addArity);
        // 除去自由值对新增变量的指向
        freeNode.iterateValid();
        while (freeNode.hasNextValid()) {
            int valIdx = freeNode.next();
            valUnmatchedVar[valIdx].remove(arity);
            valUnmatchedVar[valIdx].iterateValid();
            nodeSCC[valIdx + addArity] = -1;
        }
        inStack.clear();
        nbSCC = 0;
        // 普通变量初始化
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            nodeSCC[varIdx] = -1;
            int valIdx = var2Val[varIdx];
            nodeSCC[valIdx + addArity] = -1;
            valUnmatchedVar[valIdx].iterateValid();
        }
        // 新增变量初始化
        nodeSCC[arity] = -1;
        freeNode.iterateValid();

        //初始化early detect相关数据结构

        cycles.clear();

        if (initialProp) {
            // 开始
            int first = unvisited.nextSetBit(0);
            while (first >= 0) {
                findSCC(first);
                first = unvisited.nextSetBit(first);
            }
            initialProp = false;
        } else {
            int first = unvisited.nextSetBit(0);
            while (first >= 0) {
                if (findSCC_ED(first)) {
                    return true;
                }
                first = unvisited.nextSetBit(first);
            }
        }
        return false;
    }

    // TarjanRemoveValues
    private void findSCC(int start) {
        //initialization
        stackIdx = 0;
        // k是index
        searchIdx = -1;
        // i和j是点号，i是j的前驱
        int i = start, j = i;
        // 变量
        stepForward(i, j);
        // 变量的匹配值
        j = var2Val[i] + addArity;
        stepForward(i, j);
        i = j;
        // algo
        while (stackIdx != 0) {
            if (i >= addArity && valUnmatchedVar[i - addArity].hasNextValid()) { // i代表的是值
                j = valUnmatchedVar[i - addArity].next();
                if (unvisited.get(j)) {
                    if (!inStack.get(j)) {
                        // 变量
                        stepForward(i, j);
                        i = j;
                        if (i == arity) {// 新增变量
                            continue;
                        }
                        j = var2Val[i] + addArity;
                        stepForward(i, j);
                        i = j;
                    } else {
                        inf[i] = Math.min(inf[i], dfn[j]);
                    }
                }
            } else if (i == arity && freeNode.hasNextValid()) {// i代表的是新增变量
                // j是新增变量指向的自由值，必然不在栈中
                j = freeNode.next() + addArity;
                stepForward(i, j);
                i = j;
            } else {
                if (inf[i] == dfn[i]) {
                    int y;
                    do {
                        y = stack[--stackIdx];
                        inStack.clear(y);
                        unvisited.clear(y);
                        nodeSCC[y] = nbSCC;
                    } while (y != i);
                    nbSCC++;
                }
                inf[p[i]] = Math.min(inf[p[i]], inf[i]);
                i = p[i];
            }
        }
    }

    // Zhang20RemoveValues
    private boolean findSCC_ED(int start) {
//        unconnected = false;
        //initialization
        stackIdx = 0;
        // k是index
        searchIdx = -1;
        // i和j是点号，i是j的前驱
        int i = start, j = i;
        // 变量
        stepForward(i, j);
        // 变量的匹配值
        j = var2Val[i] + addArity;
        stepForward(i, j);
        i = j;
        // algo
        while (stackIdx != 0) {
            if (i >= addArity && valUnmatchedVar[i - addArity].hasNextValid()) { // i代表的是值
                j = valUnmatchedVar[i - addArity].next();
                if (unvisited.get(j)) {
//                    unvisited.clear(j);
                    if (!inStack.get(j)) {

                        // 变量
                        stepForward(i, j);
                        i = j;
                        if (i == arity) {// 新增变量
                            continue;
                        }
                        j = var2Val[i] + addArity;
                        stepForward(i, j);
                        i = j;
                    } else {
//                        System.out.println("curNode: " + j);
                        System.out.println("addc: i: " + i + ", j: " + j + ", infi: " + inf[i] + ", dfnj: " + dfn[j] + ", maxdfs: " + searchIdx);
                        inf[i] = Math.min(inf[i], dfn[j]);

                        // for early detect
                        if (!unconnected) {
                            System.out.println("addCycles: " + j + " " + inf[j] + " " + searchIdx);
                            addCycles(inf[j], searchIdx - 1);
                            while (!DE.empty() && inCycles(DE.peek())) {
                                DE.pop();
                            }
                        }
                    }
                }
            } else if (i == arity && freeNode.hasNextValid()) {// i代表的是新增变量
                // j是新增变量指向的自由值，必然不在栈中
                j = freeNode.next() + addArity;
                stepForward(i, j);
                i = j;
            } else {
                if (inf[i] == dfn[i]) {
                    int y;
                    do {
                        y = stack[--stackIdx];
                        inStack.clear(y);
                        unvisited.clear(y);
                        nodeSCC[y] = nbSCC;
//                        System.out.println("pop: " + y + ", " + nbSCC);
                    } while (y != i);
                    nbSCC++;
//                    unconnected = true;
                }
                inf[p[i]] = Math.min(inf[p[i]], inf[i]);
                i = p[i];

                if (!unconnected && DE.empty()) {
//                    System.out.println("xixi");
                    return true;
                }
            }
        }

        return false;
    }

    private void stepForward(int pre, int sub) {
        searchIdx++;
        dfn[sub] = searchIdx;
        inf[sub] = searchIdx;
        p[sub] = pre;
        stack[stackIdx++] = sub;
        inStack.set(sub);
    }

    private void addCycles(int a, int b) {
        var iter = cycles.iterator();
        while (iter.hasNext()) {
            tt = iter.next();
            if (tt.overlap(a, b)) {
                tt.a = Math.min(tt.a, a);
                tt.b = Math.max(tt.b, b);
                return;
            }
        }
        cycles.add(new IntPair(a, b));
    }

    private boolean inCycles(IntPair t) {
//        IntTuple2 tt;
//        System.out.println("inc:" + t.a + "," + t.b + "=" + DFSNum[t.a] + "," + DFSNum[t.b]);
        if (dfn[t.a] == -1 || dfn[t.b] == -1) {
            return false;
        }
        for (int i = 0, len = cycles.size(); i < len; ++i) {
            tt = cycles.get(i);
            if (tt.cover(dfn[t.a]) && tt.cover(dfn[t.b])) {
                return true;
            }
        }
        return false;
    }

    private boolean filter() throws ContradictionException {
        if (buildSCC()) {
            Measurer.enterSkip();
            return true;
        }
//        System.out.println(Arrays.toString(nodeSCC));
        boolean filter = false;
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
        return filter;
    }
}