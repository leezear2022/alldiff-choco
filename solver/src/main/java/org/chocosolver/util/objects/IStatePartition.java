package org.chocosolver.util.objects;

import java.util.Arrays;
import java.util.ConcurrentModificationException;

public abstract class IStatePartition {
    static int INDEX_OVERFLOW = -1;
    static int INDEX_OVER_OVERFLOW = -2;
    static int INDEX_OVER_OVER_OVERFLOW = -3;

    int[] dense;
    int[] sparse;
    int size;
    int limit;
    int maxIndex;
    int lastRet = INDEX_OVER_OVERFLOW;
    int cursor = INDEX_OVER_OVERFLOW;
    int sccEndIndex = INDEX_OVERFLOW;
    int sccStartIndex = INDEX_OVERFLOW;
    int tmpIdx = INDEX_OVER_OVER_OVERFLOW;

    public IStatePartition(int nbit) {
        size = nbit;
        maxIndex = nbit - 1;
        dense = new int[size];
        sparse = new int[size];
        for (int i = 0; i < size; i++) {
            dense[i] = i;
            sparse[i] = i;
        }
    }

    // limit operations
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

// 弃用 连续删值会有问题
//    public void removeCurrentToHead() {
//        // 调用此函数时cursor不可能在tmp中，所以不用考虑tmp的问题
//        // 只需将lastRect与sccStart交换
//        // 重新设置sccStart, lastRect = -1
//
//        /**
//         * 当前tmp有效
//         * 交换策略
//         * tmp<-sccStart
//         * sccStart<-cursor
//         * cursor<-tmp
//         * */
//
//        // 查找当前索引
//        int e = dense[lastRet];
//        int index = sparse[e];
//        // 查找边界索引
//        int index2 = sccStartIndex;
//        if (index != index2) {
//            int tmp = dense[index2];
//            sparse[e] = index2;
//            sparse[tmp] = index;
//            dense[index] = tmp;
//            dense[index2] = e;
//        }
//        // 前一处设置split
//        //sccMask.set(index2);
//        maskSet(index2);
//        sccStartIndex++;
//        lastRet = INDEX_OVER_OVERFLOW;
//    }

    private void removeCurrentToTailTmp() {
        /**
         * 当前tmp有效
         * 交换策略：
         *  tmp<-sccEnd
         *  sccEnd<-lastRect
         *  lastRect<-tmpIdx-1
         *  tmpIdx-1<-tmp
         * */
        int newTmpIdx = tmpIdx - 1;
        int tmp_e = dense[newTmpIdx];
        int e = dense[lastRet];
        int end_e = dense[sccEndIndex];

        sparse[e] = sccEndIndex;
        sparse[tmp_e] = lastRet;
        sparse[end_e] = newTmpIdx;
        dense[sccEndIndex] = dense[lastRet];
        dense[lastRet] = dense[newTmpIdx];
        dense[newTmpIdx] = dense[end_e];

        tmpIdx = newTmpIdx;

        maskSet(sccEndIndex);
        --sccEndIndex;

        if (lastRet < cursor)
            --cursor;

        lastRet = INDEX_OVER_OVERFLOW;
    }

    private void removeCurrentToTailNoTmp() {
        /**
         * 当前tmp无效
         * 交换策略：
         *  tmp<-sccEnd
         *  sccEnd<-index
         *  index<-tmp
         * */
        int e = dense[lastRet];
        int index = sparse[e];
        // 查找边界索引
        int index2 = sccEndIndex;
        if (index != index2) {
            int tmp = dense[index2];
            sparse[e] = index2;
            sparse[tmp] = index;
            dense[index] = tmp;
            dense[index2] = e;
        }

        // 前一处设置split
        maskSet(index2);
        --sccEndIndex;

        if (lastRet < cursor)
            --cursor;

        lastRet = INDEX_OVER_OVERFLOW;
    }

    public void removeCurrentToTail() {
        // 查找当前索引
        if (this.lastRet == -1) {
            throw new IllegalStateException();
        }
        if (inCurrentSCC(tmpIdx)) {
            removeCurrentToTailTmp();
        } else {
            // 当前tmp无效
            removeCurrentToTailNoTmp();
        }

    }

    public int resetLimitByElement(int e) {
        limit = getSCCStartIndex(sparse[e]);
        return limit;
    }

    // index operation
    int getSCCStartIndex(int index) {
        return maskPrevSetBit(index);
    }

    public int getSCCStartIndexByElement(int e) {
        return getSCCStartIndex(sparse[e]);
    }

    int getSCCEndIndex(int index) {
//        if (index < maxIndex) {
        int end = maskNextSetBit(index + 1) - 1;
        return end < 0 ? maxIndex : end;
//        } else {
//            return maxIndex;
//        }
//        return (index < maxIndex) ? maskNextSetBit(index + 1) - 1 : maxIndex;
    }

    public int getSCCEndIndexByElement(int e) {
        return getSCCEndIndex(sparse[e]);
    }

    void getSCCStartIndices(SparseSet s) {
        s.clear();
        for (int i = maskNextSetBit(0); i != -1; i = maskNextSetBit(i + 1)) {
            s.add(i);
        }
    }

    // size
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

    // iterator actions
    // for iteration
    public void disposeSCCIterator() {
        cursor = INDEX_OVER_OVERFLOW;
        lastRet = INDEX_OVER_OVERFLOW;
        sccEndIndex = INDEX_OVERFLOW;
        sccStartIndex = INDEX_OVERFLOW;
        tmpIdx = INDEX_OVER_OVER_OVERFLOW;
    }

    public void setIteratorIndexBySCCStartIndex(int start) {
        this.cursor = start;
        this.sccStartIndex = start;
        this.sccEndIndex = getSCCEndIndex(start);
    }

//    public boolean isValid() {
//        return iterIdx >= sccStartIndex && iterIdx <= sccEndIndex;
//    }

    public boolean hasNext() {
        return cursor >= sccStartIndex && cursor <= sccEndIndex;
    }

//    public int getValue() {
//        return dense[iterIdx];
//    }

    public int next() {
        int next = dense[cursor];
        lastRet = cursor++;
        return next;
    }

    public void next(IntBoolPair ib) {
        ib.y = cursor == tmpIdx;
        ib.x = dense[cursor++];
    }

    public void nextOrElseSetSplit(IntBoolPair ib) {
        if (cursor == tmpIdx) {
            // 当前遍历到tmp区域，tmpIdx失效，设定前方区域为独立SCC
            ib.y = true;
            disposeTmp();
            sccStartIndex = cursor;
            if (cursor != size)
                maskSet(cursor);
        } else {
            ib.y = false;
        }

        ib.x = dense[cursor];
        lastRet = cursor++;
    }

    public int nextAndSplitWhenEnteringTmp() {
        if (cursor == tmpIdx) {
            // 当前遍历到tmp区域，tmpIdx失效，设定前方区域为独立SCC
//            ib.y = true;
            disposeTmp();
            sccStartIndex = cursor;
            if (cursor != size)
                maskSet(cursor);
        }

        int next = dense[cursor];
        lastRet = cursor++;
        return next;
    }

    public int splitTmp() {
        int newStart = tmpIdx;
        maskSet(newStart);
        disposeTmp();
        return newStart;
    }

//    public void moveToTmp() {
//        tmpIdx = (tmpIdx == INDEX_OVER_OVER_OVERFLOW) ? sccEndIndex : tmpIdx - 1;
//        int e = dense[cursor];
//        int tmp = dense[tmpIdx];
//        sparse[e] = tmpIdx;
//        sparse[tmp] = cursor;
//        dense[cursor] = tmp;
//        dense[tmpIdx] = e;
//    }


    public void moveToTmp(int e) {
//        tmpIdx = (tmpIdx == INDEX_OVER_OVER_OVERFLOW) ? sccEndIndex : tmpIdx - 1;
////        int e = dense[cursor];
//        int index = sparse[e];
//        int tmp = dense[tmpIdx];
//        sparse[e] = tmpIdx;
//        sparse[tmp] = cursor;
//        dense[cursor] = tmp;
//        dense[tmpIdx] = e;

        // 查找当前索引
        int index = sparse[e];
        // 如果e的索引在tmp中则不需移动
        if (index >= tmpIdx && tmpIdx >= 0)
            return;
        // 查找边界索引
        tmpIdx = (tmpIdx == INDEX_OVER_OVER_OVERFLOW) ? sccEndIndex : tmpIdx - 1;
        if (index != tmpIdx) {
//            System.out.println("xixi");
            int tmp = dense[tmpIdx];
            sparse[e] = tmpIdx;
            sparse[tmp] = index;
            dense[index] = tmp;
            dense[tmpIdx] = e;
        }
    }

    public void disposeTmp() {
        tmpIdx = INDEX_OVER_OVER_OVERFLOW;
    }

    public void disposeIter() {
        cursor = INDEX_OVER_OVERFLOW;
    }

    public void goNext() {
        ++cursor;
    }

    public void setSplit() {
        // 若为1则表示新分区的开始
        if (limit != size)
            maskSet(limit);
    }

    public void setSplitTmp() {
        // 若为1则表示新分区的开始
        if (cursor != size)
            maskSet(cursor);
    }

    private boolean inCurrentSCC(int index) {
        return index >= sccStartIndex && index <= sccEndIndex;
    }

    /**
     * return whether node e is in the SCC of current SCC
     *
     * @param e
     * @return in same SCC
     */
    public boolean inSameSCC(int e) {
        int index = sparse[e];
        return index >= sccStartIndex && index <= sccEndIndex;
    }

    public boolean canMoveToTmp(int e) {
        int index = sparse[e];
        // lastRet不能处理
        // lastRet = INDEX_OVER_OVERFLOW;
        // 若处理 再调用removeCurrentToHead()会出错
        if (tmpIdx == INDEX_OVER_OVER_OVERFLOW) {
            return index >= cursor && index <= sccEndIndex;
        } else {
            return index >= cursor && index <= tmpIdx;
        }
    }

    public boolean hasSplit(int e) {
        int index = sparse[e];
        return index < sccStartIndex || index > sccEndIndex;

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

    abstract String maskStr();

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

    @Override
    public String toString() {
        StringBuilder ss = new StringBuilder("[");
        for (int i = 0; i < size; i++) {
//            if (sccStart.get(i)) {
            if (!maskGet(i)) {
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
                .append(maskStr());
        return ss.toString();
    }

    public class IntBoolPair {
        public int x = -1;
        public boolean y = false;

        public IntBoolPair(int x, boolean y) {
            this.x = x;
            this.y = y;
        }
    }

}
