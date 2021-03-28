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

    public int setSplit() {
        splitPoint.clear(limit);
        return limit;
    }

    public void resetIterator(int e) {
        iterIdx = splitPoint.prevClearBit(e);
    }

    public void resetLimit(int e) {
        limit = splitPoint.prevClearBit(e);
    }

    //    public getIterator()
    public boolean hasNext() {
        return splitPoint.get(iterIdx);
    }

    public int next() {
        return dense[++iterIdx];
    }


}
