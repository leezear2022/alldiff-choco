package org.chocosolver.solver.constraints.nary.alldifferent.algo;

//import org.chocosolver.amtf.Measurer;

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.map.hash.TIntIntHashMap;
import org.chocosolver.memory.IEnvironment;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.INaiveBitSet;
import org.chocosolver.util.objects.Measurer;
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
public class AlgoAllDiffAC_WordRamRegin {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************
    // 约束的个数
    static public int num = 0;

    // 约束的编号
    private int id;
    private long xixi = 0;
    protected static long numCall = -1;
    private int arity;
    private IntVar[] vars;
    private ICause aCause;

    // 新增一点（视为变量）
    private int addArity;

    // 自由值集合
    private SparseSet freeNodes;

    // 以下是bit版本所需数据结构========================
    // numValue是二部图中取值编号的个数，numBit是二部图的最大边数
    private int numValues;
    // 值到索引
    private int[] idx2Val;
    // 索引到值
    private TIntIntHashMap val2Idx;

//    // 与值相连的变量
//    private INaiveBitSet[] B;
//    private INaiveBitSet[] D;

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
    private boolean sinkIsUnvisited;

    private int endBitIndex = 64;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_WordRamRegin(IntVar[] variables, ICause cause, Model model) {
        id = num++;
        env = model.getEnvironment();
        this.vars = variables;
        aCause = cause;
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

        freeNodes = new SparseSet(numValues);
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    public boolean propagate() throws ContradictionException {
        ++numCall;
        System.out.printf("cid: %d, propagate: %d--------\n", id, numCall);
//        if (numCall <= 696 && numCall >= 693) {
            printDomains();
//        }

        Measurer.enterProp();
        startTime = System.nanoTime();
        findMaximumMatching();
        Measurer.matchingTime += System.nanoTime() - startTime;
//        if (numCall == 694)
//            System.out.println("matching: " + Arrays.toString(var2Val));
        startTime = System.nanoTime();
        boolean filter = filter();
        Measurer.filterTime += System.nanoTime() - startTime;
//        if (numCall <= 696 && numCall >= 693) {
//            System.out.println("----after----");
//            printDomains();
//        }

        return filter;
    }

    private void printDomains() {
        // 填充B和D
        System.out.println("****doms*****");
        for (int i = 0; i < arity; ++i) {
            IntVar v = vars[i];
            System.out.println(v);
        }
        System.out.println("*************");
//        // 填充B和D
//        for (int i = 0; i < arity; ++i) {
//            IntVar v = vars[i];
//            System.out.println(RD[i]);
//        }
    }

    //***********************************************************************************
    // Initialization
    //***********************************************************************************

    private void MakeAugmentingPath(int start) {
        int num_to_visit = 0;
        int num_visited = 0;
        // visit 里存的是变量
        visiting_[num_to_visit++] = start;
        unVisitedVariables.clear(start);
        variable_visited_from_[start] = -1;

        while (num_visited < num_to_visit) {
            // Dequeue node to visit.
            int node = visiting_[num_visited++];
            IntVar v = vars[node];

            for (int value = v.getLB(), ub = v.getUB(); value <= ub; value = v.nextValue(value)) {
                int valIdx = val2Idx.get(value);
                if (!unVisitedValues.get(valIdx)) continue;
                unVisitedValues.clear(valIdx);
                if (!matchedValues.get(valIdx)) {
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
                    freeNodes.remove(valIdx);
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
                    freeNodes.remove(valIdx);
                    matchedValues.set(valIdx);
                }
            }
        }
    }

    private void findMaximumMatching() throws ContradictionException {
        freeNodes.fill();
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
            if (v.getDomainSize() == 1) {
                // 取出变量的唯一值
                int valIdx = val2Idx.get(v.getValue());
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
                freeNodes.remove(valIdx);
                matchedValues.set(valIdx);
            } else {
                // 检查原匹配是否失效
                int oldMatchingIndex = var2Val[varIdx];
                if (oldMatchingIndex != -1) {
                    // 如果oldMatchingValue无效
                    if (!v.contains(idx2Val[oldMatchingIndex])) {
//                    if (!D[varIdx].get(oldMatchingIndex)) {
                        val2Var[oldMatchingIndex] = -1;
//                        unMatchedValues.set(oldMatchingIndex);
//                        matchedValues.clear(oldMatchingIndex);
                        var2Val[varIdx] = -1;
                    } else {
//                        freeNode.clear(oldMatchingIndex);
                        freeNodes.remove(oldMatchingIndex);
                        matchedValues.set(oldMatchingIndex);
//                    System.out.println(oldMatchingIndex + " is free");
                    }
                }

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

    private boolean filter() throws ContradictionException {
        boolean filter = false;
        findAllSCC();
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            IntVar v = vars[varIdx];
            if (!v.isInstantiated()) {
                for (int k = v.getLB(), ub = v.getUB(); k <= ub; k = v.nextValue(k)) {
                    int valIdx = val2Idx.get(k);
                    if (varSCC[varIdx] != valSCC[valIdx]) {
                        Measurer.enterP2();
                        if (valIdx == var2Val[varIdx]) {
                            int valNum = v.getDomainSize();
                            Measurer.numDelValuesP2 += valNum - 1;
//                            if (numCall == 694)
//                                System.out.println("instantiate  : " + valIdx + ", " + k + " P2: " + Measurer.numDelValuesP2);
                            filter |= v.instantiateTo(k, aCause);
                        } else {
                            ++Measurer.numDelValuesP2;
//                            if (numCall == 694)
//                                System.out.println("second delete: " + valIdx + ", " + k + " P2: " + Measurer.numDelValuesP2);
                            filter |= v.removeValue(k, aCause);
                        }
                    }
                }
            }
        }
        return filter;
    }

    private void findAllSCC() {
        // initialization
        clearVarStack();
        clearValStack();

        maxDFS = 0;
        nbSCC = 0;

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

        findSingletons();
        singleton.flip();
//        System.out.println("----------");
//        System.out.println("singleton:" + singleton);
//        System.out.println("singleton: " + singleton);
        for (int varIdx = singleton.firstSetBit(); varIdx != singleton.end(); varIdx = singleton.nextSetBit(varIdx + 1)) {
//            if (unVisitedVariables.get(varIdx)) {
//                System.out.println(varIdx);
//            System.out.printf("out: %d\n", varIdx);
            strongConnectVar(varIdx);
//            }
        }

//        System.out.println(Arrays.toString(varSCC));
//        System.out.println(Arrays.toString(valSCC));
    }

    private void findSingletons() {
        singleton.clear();
        for (int i = 0; i < arity; i++) {
            // 变量只有一个值，即只有匹配值
            // 若匹配边由变量指向值，若D[x]=1则表示变量x只有一个出边即匹配边，没有入边，即满足singleton条件
            IntVar v = vars[i];
            if (v.getDomainSize() == 1) {
                varSCC[i] = nbSCC;
                singleton.set(i);
                nbSCC++;
            }
        }
    }

    private void strongConnectVar(int curNode) {
        pushVarStack(curNode);
        varDFSNum[curNode] = maxDFS;
        varLowLink[curNode] = maxDFS;
        maxDFS++;
        unVisitedVariables.clear(curNode);

        int matchedVal = var2Val[curNode];
        IntVar v = vars[curNode];
        for (int a = v.getLB(), ub = v.getUB(); a <= ub; a = v.nextValue(a)) {
            int newNode = val2Idx.get(a);
            if (newNode == matchedVal) continue;
//            System.out.println("scVartoVal: " + curNode + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
//            System.out.println(curNode + ", " + (addArity + newNode) + ", " + unVisitedValues.get(newNode));
            if (!unVisitedValues.get(newNode)) {
                if (valIsInStack.get(newNode)) {
                    varLowLink[curNode] = Math.min(varLowLink[curNode], valDFSNum[newNode]);
                }
            } else {
                strongConnectVal(newNode);
                varLowLink[curNode] = Math.min(varLowLink[curNode], valLowLink[newNode]);
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
    }

    private void strongConnectVal(int curNode) {
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
                }
            } else {
                strongConnectVar(matchedVar);
                valLowLink[curNode] = Math.min(valLowLink[curNode], varLowLink[matchedVar]);
            }
        } else {
            //free node successor node is sink node
//            System.out.println("scValtoSink: " + (addArity + curNode) + ", " + arity + ", " + sinkIsUnvisited);
//            System.out.println((addArity + curNode) + ", " + arity + ", " + sinkIsUnvisited);
            if (!sinkIsUnvisited) {
                if (sinkIsInStack) {
                    valLowLink[curNode] = Math.min(valLowLink[curNode], sinkDFSNum);
                }
            } else {
                strongConnectSink();
                valLowLink[curNode] = Math.min(valLowLink[curNode], sinkLowLink);
            }
        }
//        System.out.println(curNode + " has no nei " + lowLink[curNode] + ", " + DFSNum[curNode]);
        if (valLowLink[curNode] == valDFSNum[curNode]) {
            if (valLowLink[curNode] > 0 || valIsInStack.size() + varIsInStack.size() > 0) {
                hasSCCSplit = true;
            }
            if (hasSCCSplit) {
//                int stackNode = -1;
//                sccSize = 0;
//                while (stackNode != curNode) {
//                    stackNode = popValStack();
////                    System.out.println("pop: " + stackNode + ", " + nbSCC);
//                    valSCC[stackNode] = nbSCC;
//                    sccSize++;
//                    varSCC[popVarStack()] = nbSCC;
//                    sccSize++;
//                }
////                if (sccSize == 1) {
////                    singleton.add(nbSCC);
////                }
//                nbSCC++;
                processSCC(valDFSNum[curNode]);
            }
        }
//        System.out.println("back");
    }

    private void strongConnectSink() {
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
                processSCC(sinkDFSNum);
            }
        }
//        System.out.println("back");
    }

    private void processSCC(int rootNum) {
//        for (int valIdx = valIsInStack.firstSetBit(); valIdx !=INaiveBitSet.INDEX_OVERFLOW; valIdx=valIsInStack.++) {
//
//        }
//        System.out.println("scc: " + rootNum);
        int stackNode = -1;
        sccSize = 0;
//        if (valStackIdx != 0) {
//            stackNode = valStack[valStackIdx - 1];
        while (valStackIdx > 0 && valDFSNum[valStack[valStackIdx - 1]] >= rootNum) {
            stackNode = popValStack();
//            System.out.println("pop var: " + stackNode + ", " + nbSCC + "," + valDFSNum[stackNode]);
            valSCC[stackNode] = nbSCC;
            sccSize++;
        }
//        }

//        if (varStackIdx != 0) {
//            stackNode = varStack[varStackIdx - 1];
        while (varStackIdx > 0 && varDFSNum[varStack[varStackIdx - 1]] >= rootNum) {
            stackNode = popVarStack();
//            System.out.println("pop val: " + stackNode + ", " + addArity + stackNode + ", " + nbSCC + "," + varDFSNum[stackNode]);
            varSCC[stackNode] = nbSCC;
            singleton.clear(stackNode);
            sccSize++;
        }
//        }

        if (sinkIsInStack && sinkDFSNum >= rootNum) {
            sinkIsInStack = false;
        }

        nbSCC++;
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

    public int nextSetBit(long words, int bitIndex) {
        return Long.numberOfTrailingZeros(words & -1L << bitIndex);
    }
}