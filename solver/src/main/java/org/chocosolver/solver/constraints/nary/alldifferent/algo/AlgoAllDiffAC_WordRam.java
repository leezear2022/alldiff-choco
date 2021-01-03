package org.chocosolver.solver.constraints.nary.alldifferent.algo;

//import org.chocosolver.amtf.Measurer;

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.map.hash.TIntIntHashMap;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.graphOperations.connectivity.StrongConnectivityFinderR;
import org.chocosolver.util.objects.INaiveBitSet;
import org.chocosolver.util.objects.Measurer;
import org.chocosolver.util.objects.NaiveBitSetOld;
import org.chocosolver.util.objects.SparseSet;
import org.chocosolver.util.objects.graphs.DirectedGraph;
import org.chocosolver.util.objects.setDataStructures.SetType;

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
public class AlgoAllDiffAC_WordRam {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************
    // 约束的个数
    static public int num = 0;
    // 约束的编号
    private int id;
    private long startTime;

    private int arity;
    private IntVar[] vars;
    private ICause aCause;

//    // 自由值集合
//    private SparseSet freeNode;

    // 以下是bit版本所需数据结构========================
    // numValue是二部图中取值编号的个数，numBit是二部图的最大边数
    private int numValues;
    // 值到索引
    private int[] idx2Val;
    // 索引到值
    private TIntIntHashMap val2Idx;

    // bitwise representation for B and D
    private INaiveBitSet[] B;
    private INaiveBitSet[] D;

    //    // 已访问过的变量和值
//    private NaiveBitSetOld variable_visited_;
//    private NaiveBitSetOld value_visited_;
//
    // matching
    private int[] val2Var;
    private int[] var2Val;
//
//    // 记录队列
//    private int[] visiting_;
//    private int[] variable_visited_from_;

    // 变量到变量的连通性
    // 对于惰性算法，记录是否知道-变量到变量的连通性
    private NaiveBitSetOld[] graphLinkedMatrix;
    private NaiveBitSetOld[] graphLinkedFrontier;

    // !! 记录gamma的前沿
    private NaiveBitSetOld gammaFrontier;
    // 记录gamma的bitset
    private NaiveBitSetOld gammaMask;

    private INaiveBitSet nonVisitedValues_;
    private int[] varQueue_;
    private int[] varQueueStartAtLevel_;
    private INaiveBitSet[] accessibleValues_;
    private int varQueueSize_;
    private boolean newValuesAreAccessible_;
    private int level_;

    private INaiveBitSet unmatchedValues;

    private int numMatched = 0;

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


    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************
    public AlgoAllDiffAC_WordRam(IntVar[] variables, ICause cause) {
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

        numValues = val2Idx.size();
        idx2Val = new int[numValues];
        TIntIntIterator it = val2Idx.iterator();
        while (it.hasNext()) {
            it.advance();
            idx2Val[it.value()] = it.key();
        }

        //------------------inital B and D
        B = new INaiveBitSet[numValues];
        for (int i = 0; i < numValues; ++i) {
            B[i] = INaiveBitSet.makeBitSet(arity, false);

        }

        D = new INaiveBitSet[arity];
        for (int i = 0; i < arity; ++i) {
            D[i] = INaiveBitSet.makeBitSet(numValues, false);
        }

        fillBandD();

        nonVisitedValues_ = INaiveBitSet.makeBitSet(numValues, true);
        varQueue_ = new int[arity];
        varQueueStartAtLevel_ = new int[numValues];
        accessibleValues_ = new INaiveBitSet[2];
        for (int i = 0; i < 2; i++) {
            accessibleValues_[i] = INaiveBitSet.makeBitSet(numValues, true);
        }
        unmatchedValues = INaiveBitSet.makeBitSet(numValues, true);

        var2Val = new int[arity];
        val2Var = new int[numValues];
        for (int i = 0; i < arity; ++i) {
            var2Val[i] = -1;
        }
        for (int i = 0; i < numValues; ++i) {
            val2Var[i] = -1;
        }

        gammaFrontier = new NaiveBitSetOld(arity);
        gammaMask = new NaiveBitSetOld(arity);

        graphLinkedMatrix = new NaiveBitSetOld[arity];
        graphLinkedFrontier = new NaiveBitSetOld[arity];
        for (int i = 0; i < arity; ++i) {
            graphLinkedMatrix[i] = new NaiveBitSetOld(arity);
            graphLinkedFrontier[i] = new NaiveBitSetOld(arity);
        }

        valUnmatchedVar = new SparseSet[numValues];
        for (int i = 0; i < numValues; ++i) {
            valUnmatchedVar[i] = new SparseSet(addArity);
        }
        // freeNode区分匹配点和非匹配点(正好是新增变量的取值范围）
        freeNode = new SparseSet(numValues);

        // SCC
        numNodes = addArity + numValues;
        nodeSCC = new int[numNodes];

        graph = new DirectedGraph(numNodes, SetType.BITSET, false);
        SCCfinder = new StrongConnectivityFinderR(graph);
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    public boolean propagate() throws ContradictionException {
        Measurer.enterProp();
        startTime = System.nanoTime();
        fillBandD();
        updateMatching();
        while (numMatched < arity) {
            AugmentMatching();
        }
        Measurer.matchingTime += System.nanoTime() - startTime;

        System.out.println("-----final matching-----");
        for (int i = 0; i < arity; i++) {
            System.out.println(vars[i].getName() + " match " + idx2Val[var2Val[i]]);
        }
        System.out.println("------------------");

        startTime = System.nanoTime();
        boolean filter = filter();
        Measurer.filterTime += System.nanoTime() - startTime;
        return filter;
//        return true;
    }

    //***********************************************************************************
    // Initialization
    //***********************************************************************************

    private void fillBandD() {
        for (int i = 0; i < numValues; ++i) {
            B[i].clear();
        }

        for (int i = 0; i < arity; ++i) {
            D[i].clear();
        }

        IntVar v;
        // 填充B和D
        for (int i = 0; i < arity; ++i) {
            v = vars[i];
            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
                int valIdx = val2Idx.get(j);
                D[i].set(valIdx);
                B[valIdx].set(i);
            }
        }
    }


    void updateMatching() {
        nonVisitedValues_.set();
        unmatchedValues.set();
        freeNode.fill();
        for (int varIdx = 0; varIdx < arity; varIdx++) {
            IntVar v = vars[varIdx];
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
                unmatchedValues.clear(valIdx);
                freeNode.remove(valIdx);
            } else {
                int oldMatchingIndex = var2Val[varIdx];
                if (oldMatchingIndex != -1) {
                    // 如果oldMatchingValue无效
                    if (!v.contains(idx2Val[oldMatchingIndex])) {
                        val2Var[oldMatchingIndex] = -1;
                        var2Val[varIdx] = -1;
                        unmatchedValues.clear(oldMatchingIndex);
                    } else {
                        freeNode.remove(oldMatchingIndex);
                    }
                }
            }
        }
    }

    void AugmentMatching() throws ContradictionException {

        InitVars();

        int iVar = -1;
        while (newValuesAreAccessible_) {

            INaiveBitSet currentLevelValues = accessibleValues_[level_ & 1]; // This is the one we will traverse

            level_++;
            varQueueStartAtLevel_[level_] = varQueueSize_;
            newValuesAreAccessible_ = false;

            INaiveBitSet nextLevelValues = accessibleValues_[level_ & 1]; // This is the one we will fill

            for (int iWord = 0; iWord < unmatchedValues.int64Size(); iWord++) {

                long currentLevelUnmatchedValues = currentLevelValues.getWord(iWord) & unmatchedValues.getWord(iWord);

                if (currentLevelUnmatchedValues != 0l) { // Found a path!
                    int iBit = nextSetBit(currentLevelUnmatchedValues, 0);
                    numMatched++;
                    unmatchedValues.clear(iWord * 64 + iBit);
                    ProcessPath(64 * iWord + iBit);
                    freeNode.remove(64 * iWord + iBit);
                    return;
                }

                long valuesToVisit = currentLevelValues.getWord(iWord) & nonVisitedValues_.getWord(iWord);
//                nonVisitedValues_.getWord(iWord) &= ~valuesToVisit;
                nonVisitedValues_.setWord(iWord, nonVisitedValues_.getWord(iWord) & ~valuesToVisit);

                int iVal = val2Idx.get(iWord * 64);
//                if (valuesToVisit == 0x8000000000000000) {
//                    valuesToVisit = 0x4000000000000000;
//                } else {
//                    iVal--;
//                }

                while (valuesToVisit != 0l) {

                    int delta = 1 + nextSetBit(valuesToVisit, 0);
                    iVal += delta;
                    valuesToVisit >>= delta;

                    iVar = val2Var[iVal];
                    freeNode.remove(iVal);
                    ProcessVar(iVar, nextLevelValues);
                }

            }

        }

        Measurer.matchingTime += System.nanoTime() - startTime;
        vars[0].instantiateTo(vars[0].getLB() - 1, aCause);

    }

    void InitVars() {
        newValuesAreAccessible_ = false;
        level_ = 0;
        varQueueSize_ = 0;

        accessibleValues_[0].clear();
        accessibleValues_[1].clear();
        nonVisitedValues_.clear();

        for (int iVar = 0; iVar < arity; iVar++) {
            if (var2Val[iVar] == -1)
                ProcessVar(iVar, accessibleValues_[0]);
        }
    }

    void ProcessVar(int iVar, INaiveBitSet nextLevelValues) {
        varQueue_[varQueueSize_++] = iVar;
        nextLevelValues.or(D[iVar]);
        newValuesAreAccessible_ = newValuesAreAccessible_ || !D[iVar].isEmpty();
    }

    void ProcessPath(int iVal) {
        while (--level_ >= 0) {
            int iVar = FindValueParent(iVal);
//            int iVal = val2Idx.get(value);
//            value = var2Val[iVar];
            setMatch(iVar, iVal);
        }
    }

    void setMatch(int iVar, int iVal) {
        var2Val[iVar] = iVal;
        val2Var[iVal] = iVar;
    }

    int FindValueParent(int valIdx) {

        int iVar = -1;
        int val = -1;
        IntVar v;
        for (int iQueue = varQueueStartAtLevel_[level_]; iQueue < varQueueSize_; iQueue++) {
            iVar = varQueue_[iQueue];
            v = vars[iQueue];
            val = idx2Val[valIdx];
            if (v.contains(val)) {
                return iVar;
            }
        }

        return iVar;
    }

    private int nextSetBit(long word, int pos) {
        return Long.numberOfTrailingZeros(word & -1L << pos);
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
//             varIdx != -1; varIdx = gammaFrontier.nextSetBit(0)) {
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
//                int ub = v.getUB();
//                for (int k = v.getLB(); k <= ub; k = v.nextValue(k)) {
//                    int valIdx = val2Idx.get(k);
//                    if (!notGamma.contain(varIdx) && notA.contain(valIdx)) {
//                        ++Measurer.numDelValuesP1;
//                        Measurer.enterP1();
//                        filter |= v.removeValue(k, aCause);
//                        //                System.out.println("first delete: " + v.getName() + ", " + k);
//                    } else if (notGamma.contain(varIdx) && notA.contain(valIdx)) {
//                        if (!graphLinkedMatrix[varIdx].get(val2Var[valIdx]) && !checkSCC(varIdx, valIdx)) {
//                            Measurer.enterP2();
//                            if (valIdx == var2Val[varIdx]) {
//                                int valNum = v.getDomainSize();
//                                Measurer.numDelValuesP2 += valNum - 1;
//                                filter |= v.instantiateTo(k, aCause);
////                            System.out.println("instantiate  : " + v.getName() + ", " + k);
//                            } else {
//                                ++Measurer.numDelValuesP2;
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
//             i != -1; i = graphLinkedFrontier[varIdx].nextSetBit(0)) {
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

    private void buildSCC() {

        for (int i = 0; i < numNodes; i++) {
            graph.getSuccOf(i).clear();
            graph.getPredOf(i).clear();
        }

        // 添加匹配边 var->val
        for (int i = 0; i < arity; ++i) {
            int matchedVal = var2Val[i];
            graph.addArc(i, matchedVal + addArity);

        }

        // 添加非匹配边 val->var; val->t
        for (int j = 0, k = 0; j < numValues; ++j) {
            if (freeNode.contain(j)) {
                graph.addArc(arity, j + addArity);
            }
            valUnmatchedVar[j].iterateValid();
            while (valUnmatchedVar[j].hasNextValid()) {
                k = valUnmatchedVar[j].next();
                graph.addArc(j + addArity, k);
            }
        }

        SCCfinder.findAllSCC();
        nodeSCC = SCCfinder.getNodesSCC();
//        System.out.println(Arrays.toString(nodeSCC));
//        graph.removeNode(numNodes);
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

}