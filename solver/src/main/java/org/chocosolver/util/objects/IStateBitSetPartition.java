package org.chocosolver.util.objects;

import org.chocosolver.memory.IEnvironment;
import org.chocosolver.memory.IStateBitSet;

import java.util.Arrays;

public class IStateBitSetPartition extends IStatePartition {
    IStateBitSet sccMask;

    public IStateBitSetPartition(int arity, IEnvironment e) {
        super(arity);
        sccMask = e.makeBitSet(arity);
        sccMask.set(0);
    }


    @Override
    void maskSet(int e) {
        sccMask.set(e);
    }

    @Override
    void maskClear(int e) {
        sccMask.clear(e);
    }

    @Override
    void maskClear() {
        sccMask.clear();
    }

    @Override
    boolean maskGet(int e) {
        return sccMask.get(e);
    }

    @Override
    int maskNextSetBit(int e) {
        return sccMask.nextSetBit(e);
    }

    @Override
    int maskNextClearBit(int e) {
        return sccMask.nextClearBit(e);
    }

    @Override
    int maskPrevSetBit(int e) {
        return sccMask.prevSetBit(e);
    }

    @Override
    int maskPrevClearBit(int e) {
        return sccMask.prevClearBit(e);
    }

    @Override
    String maskStr() {
        return sccMask.toString();
    }


}
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

//    @Override
//    public void reset() {
//        sccMask.clear();
//        limit = 0;
//    }

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
//        sccMask.set(index2);
//    }

//    @Override
//    public void setSplit() {
//        // 若为1则表示新分区的开始
//        if (limit != size)
//            sccMask.set(limit);
//    }

//    @Override
//    protected int getSCCStartIndex(int index) {
//        return sccMask.prevSetBit(index);
//    }

//    @Override
//    int getSCCEndIndex(int index) {
//        return sccMask.nextSetBit(index);
//    }

//    @Override
//    public boolean isSingletonByStartIndex(int index) {
//        if (index == size) {
//            return sccMask.get(index);
//        } else {
//            return sccMask.get(index) && sccMask.get(index + 1);
//        }
//    }

//    @Override
//    void getSCCStartIndices(SparseSet s) {
//        s.clear();
//        for (int i = sccMask.nextSetBit(0); i != -1; i = sccMask.nextSetBit(i + 1)) {
//            s.add(i);
//        }
//    }

//}
