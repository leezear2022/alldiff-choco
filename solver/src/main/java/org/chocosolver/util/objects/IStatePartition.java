package org.chocosolver.util.objects;

abstract class IStatePartition {
    static int INDEXOVERFLOW = -1;
    static int INDEXOVEROVERFLOW = -2;
    int[] dense;
    int[] sparse;
    int size;
    int limit;
    int iterIdx = INDEXOVERFLOW;
    int sccEndIndex = INDEXOVERFLOW;
    int sccStartIndex = INDEXOVERFLOW;
    int lastPos;

    public IStatePartition(int size) {
        this.size = size;
        this.lastPos = size - 1;
        dense = new int[size];
        sparse = new int[size];
        for (int i = 0; i < size; i++) {
            dense[i] = i;
            sparse[i] = i;
        }
    }

    abstract public void add(int e);

    abstract public void reset();

    abstract public void remove(int e);

    abstract public void setSplit();

    public int resetLimitByElement(int e) {
        limit = getSCCStartIndex(sparse[e]);
        return limit;
    }

    abstract int getSCCStartIndex(int index);

    public int getSCCStartIndexByElement(int e) {
        return getSCCStartIndex(sparse[e]);
    }

    abstract int getSCCEndIndex(int index);

    public int getSCCEndIndexByElement(int e) {
        return getSCCEndIndex(sparse[e]);
    }

    // for iteration

    public void disposeSCCIterator() {
        iterIdx = INDEXOVEROVERFLOW;
        sccEndIndex = INDEXOVERFLOW;
        sccStartIndex = INDEXOVERFLOW;
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

    public void goNext() {
        ++iterIdx;
    }

    abstract public boolean isSingletonByStartIndex(int index);

    public boolean isSingletonByElement(int e) {
        return isSingletonByStartIndex(sparse[e]);
    }

    abstract void getSCCStartIndices(SparseSet s);


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

}
