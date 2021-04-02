package org.chocosolver.util.objects;

import org.chocosolver.memory.IEnvironment;
import org.chocosolver.memory.IStateBitSet;

public class RSetPartion {
    int[] dense;
    int[] sparse;
    IStateBitSet splitPoint;
    IEnvironment env;
    int limit = -1;
    int iterIdx = -1;

    public RSetPartion(int size, IEnvironment e) {
        this.env = e;
        dense = new int[size];
        sparse = new int[size];
        for (int i = 0; i < size; i++) {
            dense[i] = i;
            sparse[i] = i;
        }
        splitPoint = env.makeBitSet(size);
        //splitPoint = 11110,111110
        splitPoint.set(0, size - 2);
    }

    public void add(int e) {
        int index = sparse[e];
        int tmp = dense[++limit];
        sparse[e] = limit;
        sparse[tmp] = index;
        dense[index] = tmp;
        dense[limit] = e;
    }

    public void remove(int e) {
        // 查找当前索引
        int index = sparse[e];
        // 查找边界索引
        int index2 = splitPoint.nextClearBit(index);
        int tmp = dense[index2];
        sparse[e] = index2;
        sparse[tmp] = index;
        dense[index] = tmp;
        dense[index2] = e;
        // 前一处设置split
        splitPoint.clear(index2 - 1);
    }

    public int setSplit() {
        splitPoint.clear(limit);
        return limit;
    }

    public void resetIteratorByElement(int e) {
        iterIdx = splitPoint.prevClearBit(sparse[e]) + 1;
    }

    public void resetLimitByElement(int e) {
        limit = splitPoint.prevClearBit(sparse[e]) + 1;
    }

    //    public getIterator()
    public boolean hasNext() {
        return splitPoint.get(iterIdx);
    }

    public int next() {
        return dense[++iterIdx];
    }

    public int getSCCStartIndexByElement(int e) {
        return splitPoint.prevClearBit(sparse[e]) + 1;
    }

    public boolean inSameSCC(int a, int b) {
        return getSCCStartIndexByElement(a) == getSCCStartIndexByElement(b);
    }

    public void setIterIdx(int iterIdx) {
        this.iterIdx = iterIdx;
    }

    public boolean greatThanOne(int startIterIdx) {
        return !splitPoint.get(startIterIdx);
    }
}
