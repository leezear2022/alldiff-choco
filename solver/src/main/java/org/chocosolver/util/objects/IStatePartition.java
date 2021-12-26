package org.chocosolver.util.objects;

abstract class IStatePartition {
    static int INDEXOVERFLOW = -1;
    static int INDEXOVEROVERFLOW = -2;
    static int INDEXOVEROVEROVERFLOW = -3;

    int[] dense;
    int[] sparse;
    int size;
    int limit;
    int iterIdx = INDEXOVERFLOW;
    int sccEndIndex = INDEXOVERFLOW;
    int sccStartIndex = INDEXOVERFLOW;
    int tmpIdx = INDEXOVEROVEROVERFLOW;

    public IStatePartition(int size) {
        this.size = size;
        dense = new int[size];
        sparse = new int[size];
        for (int i = 0; i < size; i++) {
            dense[i] = i;
            sparse[i] = i;
        }
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
        maskClear();
        limit = 0;
    }

    public void remove(int e) {
        // 查找当前索引
        int index = sparse[e];
        // 查找边界索引
        int index2 = getSCCEndIndex(index);
        //int index2 = sccEndIndex == INDEXOVERFLOW ? getSCCEndIndex(index) : sccEndIndex;
        if (index != index2) {
            int tmp = dense[index2];
            sparse[e] = index2;
            sparse[tmp] = index;
            dense[index] = tmp;
            dense[index2] = e;
        }
        // 前一处设置split
        //sccMask.set(index2);
        maskSet(index2);
    }

    public void setSplit() {
        // 若为1则表示新分区的开始
        if (limit != size)
            maskSet(limit);
    }

    public void setSplitTmp() {
        // 若为1则表示新分区的开始
        if (iterIdx != size)
            maskSet(iterIdx);
    }

    public int resetLimitByElement(int e) {
        limit = getSCCStartIndex(sparse[e]);
        return limit;
    }

    int getSCCStartIndex(int index) {
        return maskPrevSetBit(index);
    }

    public int getSCCStartIndexByElement(int e) {
        return getSCCStartIndex(sparse[e]);
    }

    int getSCCEndIndex(int index) {
        return maskNextSetBit(index);
    }

    public int getSCCEndIndexByElement(int e) {
        return getSCCEndIndex(sparse[e]);
    }

    // for iteration

    public void disposeSCCIterator() {
        iterIdx = INDEXOVEROVERFLOW;
        sccEndIndex = INDEXOVERFLOW;
        sccStartIndex = INDEXOVERFLOW;
        tmpIdx = INDEXOVEROVEROVERFLOW;
    }

    public void setIteratorIndexBySCCStartIndex(int start) {
        this.iterIdx = start;
        this.sccStartIndex = start;
        this.sccEndIndex = getSCCEndIndex(start);
    }

    public boolean isValid() {
        return iterIdx >= sccStartIndex && iterIdx <= sccEndIndex;
    }

    public boolean hasNext() {
        return iterIdx >= sccStartIndex && iterIdx <= sccEndIndex;
    }

//    public boolean goToNextValid() {
//        return ++iterIdx >= sccStartIndex && iterIdx <= sccEndIndex;
//    }

    public int getValue() {
        return dense[iterIdx];
    }

    public int next() {
        return dense[iterIdx++];
    }

    public void next(IntBoolPair ib) {
        ib.y = iterIdx == tmpIdx;
        ib.x = dense[iterIdx++];
    }

    public void nextOrElseSetSplit(IntBoolPair ib) {
        if (iterIdx == tmpIdx) {
            // 当前到tmp区域，tmpIdx失效，
            ib.y = true;
            disposeTmp();
            sccStartIndex = iterIdx;
            setSplit();
        }

        ib.x = dense[iterIdx++];
    }

    public void moveToTmp() {
        tmpIdx = (tmpIdx == INDEXOVEROVEROVERFLOW) ? sccEndIndex : tmpIdx - 1;
        int e = dense[iterIdx];
        int tmp = dense[tmpIdx];
        sparse[e] = tmpIdx;
        sparse[tmp] = iterIdx;
        dense[iterIdx] = tmp;
        dense[tmpIdx] = e;
    }


    public void disposeTmp() {
        tmpIdx = INDEXOVEROVEROVERFLOW;
    }

    public void disposeIter() {
        iterIdx = INDEXOVEROVERFLOW;
    }

    public void goNext() {
        ++iterIdx;
    }

    public boolean isSingletonByStartIndex(int index) {
        if (index == size) {
            return maskGet(index);
        } else {
            return maskGet(index) && maskGet(index + 1);
        }
    }

    public boolean isSingletonByElement(int e) {
        return isSingletonByStartIndex(sparse[e]);
    }

    void getSCCStartIndices(SparseSet s) {
        s.clear();
        for (int i = maskNextSetBit(0); i != -1; i = maskNextSetBit(i + 1)) {
            s.add(i);
        }
    }


    // 子类只需重写bit运算部分
    abstract void maskSet(int e);

    abstract void maskClear(int e);

    abstract void maskClear();

    abstract boolean maskGet(int e);

    abstract int maskNextSetBit(int e);

    abstract int maskNextClearBit(int e);

    abstract int maskPrevSetBit(int e);

    abstract int maskPrevClearBit(int e);


//    class SCCIterator {
//        private int cursor = INDEXOVEROVERFLOW;
//        int lastRet = INDEXOVERFLOW;
//
//        SCCIterator(int index) {
//            this.cursor = index;
//        }
//
//        public boolean hasNext() {
//            return this.cursor <= sccEndIndex;
//        }
//
//        public int next() {
//            try {
//                int next = dense[iterIdx];
//                this.lastRet = this.cursor++;
//                return next;
//            } catch (IndexOutOfBoundsException var2) {
//                throw new NoSuchElementException();
//            }
//        }
//
//        public void remove() {
//            if (this.lastRet == INDEXOVERFLOW) {
//                throw new IllegalStateException();
//            } else {
//                try {
//                    remove();
//                    if (this.lastRet < this.cursor) {
//                        --this.cursor;
//                    }
//
//                    this.lastRet = -1;
//                } catch (IndexOutOfBoundsException var2) {
//                    throw new ConcurrentModificationException();
//                }
//            }
//        }
//
//        public void dispose() {
//            sccEndIndex = INDEXOVERFLOW;
//            sccStartIndex = INDEXOVERFLOW;
//            cursor = INDEXOVEROVERFLOW;
//            lastRet = INDEXOVEROVERFLOW;
//        }
//
//    }

    class IntBoolPair {
        public int x = -1;
        public boolean y = false;

        public IntBoolPair(int x, boolean y) {
            this.x = x;
            this.y = y;
        }
    }

}
