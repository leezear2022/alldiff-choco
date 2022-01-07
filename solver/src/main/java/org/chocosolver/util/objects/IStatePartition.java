package org.chocosolver.util.objects;

import java.util.Arrays;

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
    int gammaEndIndex = INDEX_OVER_OVER_OVERFLOW;
    int movedIndex = INDEX_OVER_OVER_OVERFLOW;
    int unknownIndex = INDEX_OVER_OVER_OVERFLOW;

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
         *  lastRect<-movedIdx-1
         *  movedIdx-1<-tmp
         *
         *  moveIndex不会与lastRect一致，
         *  因为只要lastRect在获取到时，
         *  MovedIndex都会被检查一次。
         * */
        int newMovedIndex = movedIndex - 1;
        int moved_e = dense[newMovedIndex];
        int e = dense[lastRet];
        int end_e = dense[sccEndIndex];

        sparse[e] = sccEndIndex;
        sparse[moved_e] = lastRet;
        sparse[end_e] = newMovedIndex;
        dense[sccEndIndex] = dense[lastRet];
        dense[lastRet] = dense[newMovedIndex];
        dense[newMovedIndex] = dense[end_e];

        movedIndex = newMovedIndex;

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
        if (inCurrentSCC(movedIndex)) {
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
        unknownIndex = INDEX_OVER_OVER_OVERFLOW;
        lastRet = INDEX_OVER_OVERFLOW;
        sccEndIndex = INDEX_OVERFLOW;
        sccStartIndex = INDEX_OVERFLOW;
        movedIndex = INDEX_OVER_OVER_OVERFLOW;
    }

    public void setIteratorIndexBySCCStartIndex(int start) {
        this.sccStartIndex = start;
        this.cursor = start;
        this.unknownIndex = start;
        this.movedIndex = INDEX_OVER_OVER_OVERFLOW;
        this.sccEndIndex = getSCCEndIndex(start);
    }

    public void setIteratorIndexAfterGamma() {
//        this.sccStartIndex = gammaEndIndex+1;
        this.cursor = gammaEndIndex + 1;
//        this.unknownIndex = gammaEndIndex+1;
//        this.movedIndex = INDEX_OVER_OVER_OVERFLOW;
        this.sccEndIndex = getSCCEndIndex(0);
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
        ib.y = cursor == movedIndex;
        ib.x = dense[cursor++];
    }

    public void nextOrElseSetSplit(IntBoolPair ib) {
        if (cursor == movedIndex) {
            // 当前遍历到tmp区域，tmpIdx失效，设定前方区域为独立SCC
            ib.y = true;
            disposeMoved();
            sccStartIndex = cursor;
            if (cursor != size)
                maskSet(cursor);
        } else {
            ib.y = false;
        }

        ib.x = dense[cursor];
        lastRet = cursor++;
    }


    /***
     * 获取下一个值，如果这个值进入Unknown区，scc分区
     *
     */
    public int nextAndSplitWhenMeetingUnknownAndMoved() {
        if (cursor != sccStartIndex && cursor == unknownIndex) {
            // cursor非sccStart 且首次进入unknown区域
            // 分裂当前scc，但不置当前变量为connected
            sccStartIndex = cursor;
            // moved区域置为空此处重新计算
            disposeMoved();

            if (cursor != size)
                maskSet(cursor);
        }

        int next = dense[cursor];
        lastRet = cursor++;
        return next;
    }

    public void setCurrentConnected() {
        if (lastRet == unknownIndex) {
            // 当前元素在unknown区域内
            // 此时moved区已经移走了
            ++unknownIndex;
        }
    }

    public void addConnected(int e) {
        // 将变量e加入Connected子分区
        int index = sparse[e];
        int ub = movedIsDisable() ? sccEndIndex : movedIndex - 1;


        if (index > unknownIndex && index <= ub) {
            // 若变量索引位于 (unknownIndex, ub] 需要交换并扩容
            // 交换unknownIndex和index
            int tmp = dense[unknownIndex];
            sparse[e] = unknownIndex;
            sparse[tmp] = index;
            dense[index] = tmp;
            dense[unknownIndex] = e;
            ++unknownIndex;
        } else if (index == unknownIndex) {
            // 若变量索引==unknownIndex，仅扩容
            ++unknownIndex;
        }

        // 否则它在connected里边，不需添加。
    }

    public int splitTmp() {
        int newStart = movedIndex;
        maskSet(newStart);
        disposeMoved();
        return newStart;
    }

    public int splitGamma() {
        int newStart = gammaEndIndex + 1;
        maskSet(newStart);
//        disposeMoved();
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

    public void addMoved(int e) {
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
        if (index >= movedIndex && movedIndex >= 0)
            return;
        // 查找边界索引
        movedIndex = (movedIndex == INDEX_OVER_OVER_OVERFLOW) ? sccEndIndex : movedIndex - 1;
        if (index != movedIndex) {
//            System.out.println("xixi");
            int tmp = dense[movedIndex];
            sparse[e] = movedIndex;
            sparse[tmp] = index;
            dense[index] = tmp;
            dense[movedIndex] = e;
        }
        --movedIndex;
    }

    public void addGamma(int e) {
        // 查找当前索引
        int index = sparse[e];
        // 若当前变量在Gamma子分区则不用移动
        if (index >= 0 && index <= gammaEndIndex)
            return;

        // 获得新的gammaEndIndex
        gammaEndIndex = gammaEndIndex == INDEX_OVER_OVER_OVERFLOW ? 0 : gammaEndIndex + 1;
        if (index != gammaEndIndex) {
//            System.out.println("xixi");
            int tmp = dense[gammaEndIndex];
            sparse[e] = gammaEndIndex;
            sparse[tmp] = index;
            dense[index] = tmp;
            dense[gammaEndIndex] = e;
        }
        --gammaEndIndex;
    }

    public void disposeMoved() {
        movedIndex = INDEX_OVER_OVER_OVERFLOW;
    }

    public void disposeGamma() {
        gammaEndIndex = INDEX_OVER_OVER_OVERFLOW;
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

    public boolean varNotInSameSCC(int e) {
        int index = sparse[e];
        return index < sccStartIndex || index > sccEndIndex;
    }

    public boolean canMoveToTmp(int e) {
        int index = sparse[e];
        // lastRet不能处理
        // lastRet = INDEX_OVER_OVERFLOW;
        // 若处理 再调用removeCurrentToHead()会出错
        if (movedIndex == INDEX_OVER_OVER_OVERFLOW) {
            return index >= cursor && index <= sccEndIndex;
        } else {
            return index >= cursor && index <= movedIndex;
        }
    }

    public boolean hasSplit(int e) {
        int index = sparse[e];
        return index < sccStartIndex || index > sccEndIndex;

    }

//    public Subpartition getSubparition(int e) {
//        int index = sparse[e];
//        if (isInvalid(index)) {
//            return Subpartition.Invalid;
//        }
//        return Subpartition.AfterSCC;
//    }


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

    public enum Subpartition {
        Invalid, BeforeSCC, Connected, Unknown, Moved, UnknownAndMoved, AfterSCC,
    }


    public boolean isInvalid(int index) {
        return index < 0;
    }

    public boolean movedIsDisable() {
        return movedIndex == INDEX_OVER_OVER_OVERFLOW;
    }

    public boolean movedIsEnable() {
        return movedIndex > 0;
    }

    public boolean beforeCurrentSCC(int index) {
        return index >= 0 && index < sccStartIndex;
    }

    public boolean isInConnected(int index) {
        return index >= sccStartIndex && index < unknownIndex;
    }


    public boolean isInUnknown(int index) {
        return index >= unknownIndex && index < movedIndex;
    }

    public boolean isInMoved(int index) {
        return movedIsDisable() ? false : index >= movedIndex && index <= sccEndIndex;
    }

    public boolean unknownMeetsMoved() {
        return (!movedIsDisable()) && unknownIndex == movedIndex;
    }

    public boolean meetsUnknown(int index) {
        return index == unknownIndex;
    }

    public boolean isUnknownAndMoved(int index) {
        return movedIsDisable() ? false : index == movedIndex && movedIndex == unknownIndex;
    }

    public boolean AfterCurrentSCC(int index) {
        return index > sccEndIndex;
    }


    public boolean currentInChecked() {
        return isInConnected(sparse[lastRet]);
    }

    public boolean varInConnected(int e) {
        int index = sparse[e];
        return index >= sccStartIndex && index < unknownIndex;
    }

    public boolean varInUnknown(int e) {
        int index = sparse[e];
        if (movedIndex == INDEX_OVER_OVER_OVERFLOW) {
            // moved区不可用
            return index >= unknownIndex && index <= sccEndIndex;
        } else {
            // moved区可用
            return index >= unknownIndex && index < movedIndex;
        }
    }

    public boolean varInMoved(int e) {
        int index = sparse[e];
        return movedIsDisable() ? false : index >= movedIndex && index <= sccEndIndex;
    }
}
