//package org.chocosolver.util.objects;
//
//import org.chocosolver.memory.IEnvironment;
//import org.chocosolver.memory.IStateInt;
//
//public class IStateIntPartition extends IStatePartition {
//    IStateInt sccMask;
//    int currentValue;
//    private static final int WORD_MASK = 0xffffffff;
//
//    IStateIntPartition(int arity, IEnvironment e) {
//        super(arity);
//        sccMask = e.makeInt();
//        setBit(sccMask, 0);
//    }
//
//    @Override
//    public void add(int e) {
//        int index = sparse[e];
//        int tmp = dense[limit];
//        sparse[e] = limit;
//        sparse[tmp] = index;
//        dense[index] = tmp;
//        dense[limit] = e;
////        varMask.set(index, varMask.get(limit));
////        varMask.set(limit, varMask.get(index));
////        varMask.set(limit, e < arity);
////        varMask.set(index, tmp < arity);
//        ++limit;
//    }
//
//    @Override
//    public void reset() {
//
//    }
//
//    @Override
//    public void remove(int e) {
//
//    }
//
//    @Override
//    public void setSplit() {
//
//    }
//
//    @Override
//    protected int getSCCStartIndex(int index) {
//        return 0;
//    }
//
//    @Override
//    int getSCCEndIndex(int e) {
//        return 0;
//    }
//
//    @Override
//    public boolean isSingletonByStartIndex(int index) {
//        return false;
//    }
//
//    @Override
//    public boolean isSingletonByElement(int e) {
//        return false;
//    }
//
//    @Override
//    void getSCCStartIndices(SparseSet s) {
//
//    }
//
//    // for bitwise operation
//    void setBit(IStateInt s, int e) {
//        currentValue = s.get();
//        s.set(currentValue | (1 << e));
//    }
//
//    void clearBit(IStateInt s, int e) {
//        currentValue = s.get();
//        s.set(currentValue & (~(1 << e)));
//    }
//
//    void clearBit(IStateInt s) {
//        s.set(0);
//    }
//
//    int nextSetBit(IStateInt s, int e) {
//        if (e >= 32)
//            return -1;
//        int currentValue = s.get() & (WORD_MASK << e);
//        return (currentValue == 0) ? INDEXOVERFLOW : Integer.numberOfTrailingZeros(currentValue);
//    }
//
//    int nextClearBit(IStateInt s, int e) {
//        if (e >= 32)
//            return -1;
//        int currentValue = ~s.get() & (WORD_MASK << e);
//        return (currentValue == 0) ? INDEXOVERFLOW : Integer.numberOfTrailingZeros(currentValue);
//    }
//
//    int prevSetBit(IStateInt s, int e) {
//        if (e < 0)
//            return -1;
//        int currentValue = s.get() & (WORD_MASK >>> -(e + 1));
//        return (currentValue == 0) ? INDEXOVERFLOW : Integer.numberOfLeadingZeros(currentValue);
//    }
//
//    int prevClearBit(IStateInt s, int e) {
//        if (e < 0)
//            return -1;
//        int currentValue = ~s.get() & (WORD_MASK >>> -(e + 1));
//        return (currentValue == 0) ?  INDEXOVERFLOW : 31 -Integer.numberOfLeadingZeros(currentValue);
//    }
//
//}
