package org.chocosolver.util.objects;

import org.chocosolver.memory.IEnvironment;
import org.chocosolver.memory.IStateLong;

public class IStateLongPartition extends IStatePartition {
    IStateLong sccMask;
    static long WORD_MASK = 0xffffffffffffffffL;
    private static final int ADDRESS_BITS_PER_WORD = 6;
    private static final int BITS_PER_WORD = 1 << ADDRESS_BITS_PER_WORD;
    private static final int BIT_INDEX_MASK = BITS_PER_WORD - 1;
//    long currentValue;currentValue

    public IStateLongPartition(int arity, IEnvironment e) {
        super(arity);
        sccMask = e.makeLong();
        //1000,0100
        // scc start with 1bit
        maskSet(0);
    }

    //for bitwise operation
    @Override
    void maskSet(int e) {
        sccMask.set(sccMask.get() | (1 << e));
    }

    @Override
    void maskClear(int e) {
        sccMask.set(sccMask.get() & (~(1 << e)));
    }

    @Override
    void maskClear() {
        sccMask.set(0);
    }

    @Override
    boolean maskGet(int e) {
        return (sccMask.get() & (1L << e)) != 0;
    }

    @Override
    int maskNextSetBit(int e) {
        if (e >= BITS_PER_WORD)
            return INDEX_OVERFLOW;
        long currentValue = sccMask.get() & (WORD_MASK << e);
        return (currentValue == 0) ? INDEX_OVERFLOW : Long.numberOfTrailingZeros(currentValue);
    }

    @Override
    int maskNextClearBit(int e) {
        if (e >= BITS_PER_WORD)
            return -1;
        long currentValue = ~sccMask.get() & (WORD_MASK << e);
        return (currentValue == 0) ? INDEX_OVERFLOW : Long.numberOfTrailingZeros(currentValue);
    }

    @Override
    int maskPrevSetBit(int e) {
        if (e < 0)
            return -1;
        long currentValue = sccMask.get() & (WORD_MASK >>> -(e + 1));
        return (currentValue == 0) ? INDEX_OVERFLOW : Long.numberOfTrailingZeros(currentValue);
    }

    @Override
    int maskPrevClearBit(int e) {
        if (e < 0)
            return -1;
        long currentValue = ~sccMask.get() & (WORD_MASK >>> -(e + 1));
        return (currentValue == 0) ? INDEX_OVERFLOW : BIT_INDEX_MASK - Long.numberOfLeadingZeros(currentValue);
    }

    @Override
    String maskStr() {
        return sccMask.toString();
    }
}


//
//    @Override
//    public void add(int e) {
//        int index = sparse[e];
//        int tmp = dense[limit];
//        sparse[e] = limit;
//        sparse[tmp] = index;
//        dense[index] = tmp;
//        dense[limit] = e;
//        ++limit;
//    }
//
//    @Override
//    public void reset() {
//        clear(sccMask);
//        limit = 0;
//    }
//
//    @Override
//    public void remove(int e) {
//        // 查找当前索引
//        int index = sparse[e];
//        // 查找边界索引
//        int index2 = getSCCEndIndex(index);
////        int index2 = sccEndIndex == INDEXOVERFLOW ? getSCCEndIndex(index) : sccEndIndex;
//        if (index != index2) {
//            int tmp = dense[index2];
//            sparse[e] = index2;
//            sparse[tmp] = index;
//            dense[index] = tmp;
//            dense[index2] = e;
//        }
//        // 前一处设置split
//        set(sccMask, index2);
//    }
//
//    @Override
//    public void setSplit() {
//        // 若为1则表示新分区的开始
//        if (limit != size)
//            set(sccMask, limit);
//    }
//
//    @Override
//    protected int getSCCStartIndex(int index) {
//        return prevSetBit(sccMask, index);
//    }
//
//    @Override
//    int getSCCEndIndex(int index) {
//        return nextSetBit(sccMask, index);
//    }
//
//    @Override
//    public boolean isSingletonByStartIndex(int index) {
//        if (index == size) {
//            return get(sccMask, index);
//        } else {
//            return get(sccMask, index) && get(sccMask, index + 1);
//        }
//    }
//
//    @Override
//    void getSCCStartIndices(SparseSet s) {
//        s.clear();
//        for (int i = nextSetBit(sccMask, 0); i != -1; i = nextSetBit(sccMask, i + 1)) {
//            s.add(i);
//        }
//    }

//
//    //for bitwise operation
//    void set(IStateLong s, int e) {
//        long currentValue = s.get();
//        s.set(currentValue | (1 << e));
//    }
//
//    void clear(IStateLong s, int e) {
//        long currentValue = s.get();
//        s.set(currentValue & (~(1 << e)));
//    }
//
//    void clear(IStateLong s) {
//        s.set(0);
//    }
//
//    boolean get(IStateLong s, int e) {
//        return (s.get() & (1L << e)) != 0;
//    }
//
//    static int nextSetBit(IStateLong s, int e) {
//        if (e >= BITS_PER_WORD)
//            return -1;
//        long currentValue = s.get() & (WORD_MASK << e);
//        return (currentValue == 0) ? INDEXOVERFLOW : Long.numberOfTrailingZeros(currentValue);
//    }
//
//
//    static int nextClearBit(IStateLong s, int e) {
//        if (e >= BITS_PER_WORD)
//            return -1;
//        long currentValue = ~s.get() & (WORD_MASK << e);
//        return (currentValue == 0) ? INDEXOVERFLOW : Long.numberOfTrailingZeros(currentValue);
//    }
//
//    static int prevSetBit(IStateLong s, int e) {
//        if (e < 0)
//            return -1;
//        long currentValue = s.get() & (WORD_MASK >>> -(e + 1));
//        return (currentValue == 0) ? INDEXOVERFLOW : Long.numberOfLeadingZeros(currentValue);
//    }
//
//    static int prevClearBit(IStateLong s, int e) {
//        if (e < 0)
//            return -1;
//        long currentValue = ~s.get() & (WORD_MASK >>> -(e + 1));
//        return (currentValue == 0) ? INDEXOVERFLOW : BIT_INDEX_MASK - Long.numberOfLeadingZeros(currentValue);
//    }
//}
