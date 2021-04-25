package org.chocosolver.util.objects;

import gnu.trove.set.hash.TIntHashSet;
import org.chocosolver.memory.IEnvironment;
import org.chocosolver.memory.IStateBitSet;

import java.util.Arrays;

public class RSetPartition {
    int[] dense;
    int[] sparse;
    IStateBitSet sccStart;
    IEnvironment env;
    int limit = 0;
    int iterIdx = -1;
    int size;
    int lastPos;

    public RSetPartition(int size, IEnvironment e) {
        this.size = size;
        this.lastPos = size - 1;
        this.env = e;
        dense = new int[size];
        sparse = new int[size];
        for (int i = 0; i < size; i++) {
            dense[i] = i;
            sparse[i] = i;
        }
        // 0标记SCC的开头
        sccStart = env.makeBitSet(size);
        //splitPoint = 011110,11111
        sccStart.set(1, size);
    }

    public void add(int e) {
        int index = sparse[e];
        int tmp = dense[limit];
        sparse[e] = limit;
        sparse[tmp] = index;
        dense[index] = tmp;
        dense[limit] = e;
        ++limit;
    }

    public void reset() {
        sccStart.set(1, size);
        limit = 0;
    }

    public void remove(int e) {
        // 查找当前索引
        int index = sparse[e];
        // 查找边界索引
        int index2 = getSCCEndIndex(index);
        if (index != index2) {
            int tmp = dense[index2];
            sparse[e] = index2;
            sparse[tmp] = index;
            dense[index] = tmp;
            dense[index2] = e;
        }
        // 前一处设置split
        sccStart.clear(index2);
    }

    public void setSplit() {
        // 若为0则表示新分区的开始
        if (limit != size)
            sccStart.clear(limit);
    }

    public int resetIteratorByElement(int e) {
        iterIdx = getSCCStartIndex(sparse[e]);
        return iterIdx;
    }

    public int resetLimitByElement(int e) {
        limit = getSCCStartIndex(sparse[e]);
        return limit;
    }

    public boolean hasNext() {
        return iterIdx != size && sccStart.get(iterIdx);
    }

    public int next() {
        return dense[iterIdx++];
    }

    public int getValue() {
        return dense[iterIdx];
    }

    // iter go next and test valid;
    public boolean nextValid() {
        return ++iterIdx != size && sccStart.get(iterIdx);
    }

    private int getSCCEndIndex(int index) {
        return index == size ? size : sccStart.nextClearBit(index + 1) - 1;
    }

    private int getSCCStartIndex(int index) {
        return sccStart.prevClearBit(index);
    }

    public int getSCCStartIndexByElement(int e) {
        return getSCCStartIndex(sparse[e]);
    }

    public boolean inSameSCC(int a, int b) {
        return getSCCStartIndexByElement(a) == getSCCStartIndexByElement(b);
    }

    public void setIteratorIndex(int iterIdx) {
        this.iterIdx = iterIdx;
    }

    public boolean greatThanOne(int startIterIdx) {
        return !sccStart.get(startIterIdx);
    }

    public boolean isSingleton(int varID) {
        // 如果varID是0且它的后一个也是0 那么它是singleton的
        int index = sparse[varID];
        if (index == size) {
            return !sccStart.get(index);
        } else {
            return !sccStart.get(index) && !sccStart.get(index + 1);
        }
    }

    public void getSCCStartIndex(TIntHashSet indices) {
        indices.clear();
        for (int i = sccStart.nextClearBit(0); i < size; i = sccStart.nextClearBit(i + 1)) {
            indices.add(i);
        }
    }

    @Override
    public String toString() {
        StringBuilder ss = new StringBuilder("[");
        for (int i = 0; i < size; i++) {
            if (sccStart.get(i)) {
                ss.append(dense[i]).append(" ");
            } else {
                ss.append("| ").append(dense[i]).append(" ");
            }
        }

        ss.append("] ")
                .append("dense: ")
                .append(Arrays.toString(dense))
                .append(", sparse: ")
                .append(Arrays.toString(sparse))
                .append(", split:")
                .append(sccStart.toString());
        return ss.toString();
    }
}
