package org.chocosolver.solver.constraints.nary.alldifferent.algo;

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.map.hash.TIntIntHashMap;
import org.chocosolver.memory.IEnvironment;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;

public abstract class AlgoAllDiffAC_Simple {
    // 约束的个数

    static public int INDEX_OVERFLOW = -1;

    // 约束的编号
    protected int id;
    protected int arity;
    protected IntVar[] vars;
    protected ICause aCause;
    // 新增一点（视为变量）
    // 自由值集合
//    private SparseSet freeNode;
    // 以下是bit版本所需数据结构========================
    // numValue是二部图中取值编号的个数，numBit是二部图的最大边数
    protected int numValues;
    // 值到索引
    protected int[] idx2Val;
    // 索引到值
    protected TIntIntHashMap val2Idx;
    // Xc-Γ(A)
//    private SparseSet notGamma;
    // Dc-A
//    private SparseSet notA;
//    // 与值相连的变量
//    private SimpleBitSet[] B;
//    private SimpleBitSet[] D;
    protected IEnvironment env;

    public AlgoAllDiffAC_Simple(IntVar[] variables, ICause cause) {
        vars = variables;
        aCause = cause;
        arity = vars.length;
        val2Idx = new TIntIntHashMap();
        hashValues();
    }

    public AlgoAllDiffAC_Simple(IntVar[] variables, ICause cause, IEnvironment e) {

        env = e;
        vars = variables;
        aCause = cause;
        arity = vars.length;
        val2Idx = new TIntIntHashMap();
        hashValues();

    }

    public int hashValues() {
        // 先将从0开始的变量论域进行编码，只编一个变量
        for (int i = 0; i < arity; ++i) {
            IntVar v = vars[i];
            if (v.getLB() == 0) {
                for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
                    if (!val2Idx.containsKey(j)) {
                        val2Idx.put(j, val2Idx.size());
                    }
                }
                break;
            }
        }

        // 全部从头编码
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

        return numValues;
    }

    public abstract boolean propagate() throws ContradictionException;
}
