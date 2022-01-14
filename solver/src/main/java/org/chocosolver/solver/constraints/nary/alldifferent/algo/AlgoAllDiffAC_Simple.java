package org.chocosolver.solver.constraints.nary.alldifferent.algo;

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.map.hash.TIntIntHashMap;
import org.chocosolver.memory.IEnvironment;
import org.chocosolver.memory.IStateLong;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.IStateBitSetPartition;
import org.chocosolver.util.objects.IStateLongPartition;
import org.chocosolver.util.objects.IStatePartition;

import java.util.BitSet;

public abstract class AlgoAllDiffAC_Simple {
    // 约束的个数
    protected static int INDEX_OVERFLOW = -1;
    protected static final int ADDRESS_BITS_PER_WORD = 6;
    protected static final int BITS_PER_WORD = 1 << ADDRESS_BITS_PER_WORD;
    protected static final int BIT_INDEX_MASK = BITS_PER_WORD - 1;
    protected static final long WORD_MASK = 0xffffffffffffffffL;
    protected static int num = 0;
    protected static long numCall = -1;
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

    // 需赋值或删值的变量，保证这些事件顺序进行，每轮需重置
    protected BitSet changedVars;
    // 0=删值 1=赋值
    protected BitSet changedType;
    // 待处理的值
    protected BitSet[] changedVals;

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

        changedVars = new BitSet(arity);
        changedType = new BitSet(arity);
        changedVals = new BitSet[arity];
        for (int i = 0; i < arity; i++) {
            changedVals[i] = new BitSet(numValues);
        }
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

    protected IStatePartition makePartition(int size, IEnvironment e) {
        if (size <= 64) {
            return new IStateLongPartition(size, e);
        } else {
            return new IStateBitSetPartition(size, e);
        }
    }

    public abstract boolean propagate() throws ContradictionException;

    protected abstract void removeValueR(int varIdx, int valIdx);

    protected abstract void instantiateToR(int varIdx, int valIdx);

    // for keep prop Q same order with Regin algo
    protected void recordRemoveVal(int varIdx, int valIdx) {
        if (!changedVars.get(varIdx)) {
            changedVals[varIdx].clear();
        }
        changedVars.set(varIdx);
        changedType.clear(varIdx);
        changedVals[varIdx].set(valIdx);
        removeValueR(varIdx, valIdx);
    }

    // for keep prop Q same order with Regin algo
    protected void recordInstVar(int varIdx, int valIdx) {
        changedVars.set(varIdx);
        changedType.set(varIdx);
        changedVals[varIdx].clear();
        changedVals[varIdx].set(valIdx);
        instantiateToR(varIdx, valIdx);
    }

    protected void dealChanges() throws ContradictionException {
        for (int i = changedVars.nextSetBit(0); i >= 0;
             i = changedVars.nextSetBit(i + 1)) {
            IntVar v = vars[i];
            if (changedType.get(i)) {
                // inst val
                int valIdx = changedVals[i].nextSetBit(0);
                v.instantiateTo(idx2Val[valIdx], aCause);
//                System.out.println("instantiate:\t" + i + ", " + valIdx);
            } else {
                // rem val
                for (int j = changedVals[i].nextSetBit(0); j > 0;
                     j = changedVals[i].nextSetBit(j + 1)) {
                    v.removeValue(idx2Val[j], aCause);
//                    System.out.println("second delete:\t" + i + ", " + j);
                }
            }
        }
    }

//    protected static void set(IStateLong a) {
//        a.set(lastMask);
//    }

    protected static void clear(IStateLong a) {
        a.set(0);
    }

    protected static void set(IStateLong a, int e) {
        a.set(a.get() | (1l << e));
    }

    protected static void set(IStateLong a, Integer e) {
        a.set(a.get() | (1l << e));
    }


    protected static void setBit(IStateLong a, int e) {
        a.set(a.get() | (1l << e));
    }

    protected static void setBit(IStateLong a, Integer e) {
        a.set(a.get() | (1l << e));
    }

    protected static void clear(IStateLong a, int e) {
        a.set(a.get() & (~(1l << e)));
    }


//    protected static void clear(long a) {
//        a = 0;
//    }
//
//    protected static void set(long a) {
//        a = lastMask;
//    }
//
//    protected static void set(long a, int e) {
//        a |= (1 << e);
//    }
//
//    protected static void clear(long a, int e) {
//        a &= (~(1 << e));
//    }

    protected static boolean get(IStateLong a, int e) {
        return (a.get() & (1L << e)) != 0;
    }

    protected static boolean get(long a, int e) {
        return (a & (1L << e)) != 0;
    }

    protected static int nextSetBit(IStateLong a, int e) {
        if (e >= BITS_PER_WORD)
            return INDEX_OVERFLOW;
        long currentValue = a.get() & (WORD_MASK << e);
        return (currentValue == 0) ? INDEX_OVERFLOW : Long.numberOfTrailingZeros(currentValue);
    }

    protected static int nextSetBit(long a, int e) {
        if (e >= BITS_PER_WORD)
            return INDEX_OVERFLOW;
        long currentValue = a & (WORD_MASK << e);
        return (currentValue == 0) ? INDEX_OVERFLOW : Long.numberOfTrailingZeros(currentValue);
    }

    protected static int nextSetBitNew(long word, int pos) {
        return Long.numberOfTrailingZeros(word & -1L << pos);
    }

    protected static int nextSetBitNew(IStateLong word, int pos) {
        return Long.numberOfTrailingZeros(word.get() & -1L << pos);
    }

    protected static long initLastMask(int size) {
        return WORD_MASK >>> (BITS_PER_WORD - (size % BITS_PER_WORD));
    }

}
