package org.chocosolver.util.objects;

import gnu.trove.set.hash.TIntHashSet;
import org.chocosolver.memory.IEnvironment;
import org.chocosolver.memory.IStateBitSet;

import java.util.Arrays;
import java.util.BitSet;

public class RSetPartitionBakBak {
    static int INDEXOVERFLOW = -1;

    int[] dense;
    int[] sparse;

    IStateBitSet sccStartMask;
    IStateBitSet varMask;
    IEnvironment env;

    int size;
    int numVars;
    int numVals;
    int lastPos;
    int sinkIndex;

    int limit = INDEXOVERFLOW;
    int cursor = INDEXOVERFLOW;
    int sccEndIndex = INDEXOVERFLOW;
    int sccStartIndex = INDEXOVERFLOW;
    int tmpStartIndex = INDEXOVERFLOW;

    // 是否启用临时标记
//    boolean isIteratorEnable=false;
//    boolean isLimitEnable= false;
//    boolean isSccEndEnable =false;
//    boolean isSccStartEnable=false;
//    boolean isTmpEnable=false;
//    boolean isInSCCMode = false;
//    IStateBitSet valMask;

    public RSetPartitionBakBak(int size, IEnvironment e) {

    }

    public RSetPartitionBakBak(int numVars, int numVals, IEnvironment e) {
        this.numVars = numVars;
        this.numVals = numVals;
        this.lastPos = numVars + numVals;
        this.size = numVals + numVals + 1;
        this.env = e;
        this.sinkIndex = numVars;

        dense = new int[size];
        sparse = new int[size];
        for (int i = 0; i < size; i++) {
            dense[i] = i;
            sparse[i] = i;
        }

        // 1标记SCC的开头
        //splitPoint = 10001,00000
        sccStartMask = env.makeBitSet(size);
        sccStartMask.set(0);

        varMask = env.makeBitSet(size);
        // sink节点暂时算val
        varMask.set(0, numVars);
//        valMask = env.makeBitSet(size);
//        valMask.set(numVars + 1, size);
    }

    public void add(int e) {
//        System.out.println("limit: " + limit);
//        NodeType type = getNodeType(e);
        int index = sparse[e];
        int tmp = dense[limit];
        sparse[e] = limit;
        sparse[tmp] = index;
        dense[index] = tmp;
        varMask.set(index, varMask.get(tmp));
        dense[limit] = e;

        ++limit;
    }

    public void reset() {
        sccStartMask.clear();
        sccStartMask.set(0);
        varMask.clear();
        varMask.set(0, numVars);
        limit = INDEXOVERFLOW;
    }

    public int remove(int e) {
        // 查找当前索引
        int index = sparse[e];
        // 查找边界索引
        int index2 = sccEndIndex == INDEXOVERFLOW ? getSCCEndIndex(index) : sccEndIndex;
        if (index != index2) {
            int tmp = dense[index2];
            sparse[e] = index2;
            sparse[tmp] = index;
            dense[index] = tmp;
            varMask.set(index, varMask.get(tmp));
            dense[index2] = e;
            varMask.set(index2, varMask.get(e));
        }
        // 前一处设置split
        sccStartMask.set(index2);
        return --sccEndIndex;
    }
//
//    public int remove(int e, int sccEndIndex) {
//        // 查找当前索引
//        int index = sparse[e];
//        // 查找边界索引
//        int index2 = sccEndIndex;
//        if (index != index2) {
//            int tmp = dense[index2];
//            sparse[e] = index2;
//            sparse[tmp] = index;
//            dense[index] = tmp;
//            varMask.set(index, varMask.get(tmp));
//            dense[index2] = e;
//            varMask.set(index2, varMask.get(e));
//        }
//        // 前一处设置split
//        sccStartMask.set(index2);
//        return index2 - 1;
//    }

//    public int removeToTmp(int e) {
//        //若无临时区域
//        if (tmpStartIndex == -1) {
//            // 查找当前索引
//            int index = sparse[e];
//            // 查找边界索引
//            tmpStartIndex = getSCCEndIndex(index);
//            if (index != tmpStartIndex) {
//                int tmp = dense[tmpStartIndex];
//                sparse[e] = tmpStartIndex;
//                sparse[tmp] = index;
//                dense[index] = tmp;
//                dense[tmpStartIndex] = e;
//            }
//            // 前一处设置split
//            sccStart.clear(tmpStartIndex);
//        } else {
//            // 查找当前索引
//            int index = sparse[e];
//            tmpStartIndex--;
//            // 查找边界索引
//            if (index != tmpStartIndex) {
//                int tmp = dense[tmpStartIndex];
//                sparse[e] = tmpStartIndex;
//                sparse[tmp] = index;
//                dense[index] = tmp;
//                dense[tmpStartIndex] = e;
//            }
//        }
//        return tmpStartIndex;
//        // 前一处设置split
////        sccStart.clear(index2);
//    }
//
//    public void clearTmp() {
//        tmpStartIndex = -1;
//    }

    public void setSplit() {
        // 若为0则表示新分区的开始
        if (limit != size)
            sccStartMask.set(limit);
    }

    public int resetIteratorByElement(int e) {
        sccStartIndex = getSCCStartIndex(sparse[e]);
        cursor = sccStartIndex;
        sccEndIndex = getSCCEndIndex(sparse[e]);
        return cursor;
    }

    public int resetLimitByElement(int e) {
        sccStartIndex = getSCCStartIndex(sparse[e]);
        limit = sccStartIndex;
        sccEndIndex = getSCCEndIndex(sparse[e]);
        return limit;
    }

    public void disposeIterator() {
        cursor = INDEXOVERFLOW;
    }

    public void disposeLimit() {
        limit = INDEXOVERFLOW;
    }
//    public boolean hasNextValid() {
//        return iterIdx != size && !sccStart.get(iterIdx);
//    }

//    public int next() {
//        return dense[iterIdx++];
//    }

    // 用的多
    public int getValid() {
        return dense[cursor];
    }

    // iter go next and test valid;
    public boolean goToNextValid() {
        return ++cursor != size && cursor <= sccEndIndex;
    }

    public boolean goToNextValidVar() {
        int nextVarIndex = varMask.nextSetBit(cursor + 1);
        return nextVarIndex != -1 && nextVarIndex <= sccEndIndex;
    }

//    // iter go next and test valid;
//    public boolean hasNextValidVar() {
//        return sccStart.nextSetBit(iterIdx);
//    }

    private int getSCCEndIndex(int index) {
        return index < lastPos ? sccStartMask.nextSetBit(index + 1) - 1 : lastPos;
    }

    private int getSCCStartIndex(int index) {
        return sccStartMask.prevSetBit(index);
    }

    public int getSCCStartIndexByElement(int e) {
        return getSCCStartIndex(sparse[e]);
    }

    public boolean inSameSCC(int a, int b) {
        return getSCCStartIndexByElement(a) == getSCCStartIndexByElement(b);
    }

    public void setIteratorIndex(int iterIdx) {
        this.cursor = iterIdx;
    }

    public boolean greatThanOne(int startIterIdx) {
        // 比scc比1多
        return !isSingleton(startIterIdx);
//        int index = sparse[startIterIdx];
//        if (index < size) {
//            return sccStart.get(index) && sccStart.get(index + 1);
//        }
//        return false;
    }

    public int partitionSize(int startIterIdx) {
        return getSCCEndIndex(startIterIdx) - getSCCStartIndex(startIterIdx);
    }

    public boolean isSingleton(int varID) {
        // 如果varID是1且它的后一个也是1 那么它是singleton的
        int index = sparse[varID];
        if (index == size) {
            return sccStartMask.get(index);
        } else {
            return sccStartMask.get(index) && sccStartMask.get(index + 1);
        }
    }

    public void getSCCStartIndex(TIntHashSet indices) {
        indices.clear();
        for (int i = sccStartMask.nextClearBit(0); i < size; i = sccStartMask.nextClearBit(i + 1)) {
            indices.add(i);
        }
    }

    public void getPartitionVars(int sccStartIndex, SparseSet vars) {
//        restriction.clear();
        vars.clear();
        for (int i = varMask.nextSetBit(sccStartIndex), end = varMask.nextSetBit(getSCCEndIndex(sccStartIndex)); i < end; i = varMask.nextSetBit(i + 1)) {
            vars.add(i);
        }
    }

    public void getPartitionBitSetMask(int sccStartIndex, BitSet restriction) {
        restriction.clear();
        for (int i = varMask.nextSetBit(sccStartIndex), end = varMask.nextSetBit(getSCCEndIndex(sccStartIndex)); i < end; i = varMask.nextSetBit(i + 1)) {
            restriction.set(dense[i]);
        }
    }

    public void getPartitionBitSetMaskAndVars(int sccStartIndex, BitSet restriction, SparseSet vars, SparseSet vals, int arity, int numValue) {
        restriction.clear();
        vars.clear();
        vals.clear();
        int addArity = arity + 1;
        for (int i = sccStartIndex, end = getSCCEndIndex(sccStartIndex); i <= end; i++) {
            int valIdx = dense[i];
            restriction.set(valIdx);
        }

        for (int i = restriction.nextSetBit(0); i != -1 && i < arity; i = restriction.nextSetBit(i + 1)) {
            vars.add(i);
        }

        for (int i = restriction.nextSetBit(addArity), ub = addArity + numValue; i != -1 && i < ub; i = restriction.nextSetBit(i + 1)) {
            vals.add(i - addArity);
        }
    }

    public void getPartitionBitSetMaskAndVars(int sccStartIndex, BitSet restriction, SparseSet vars, SparseSet vars2, SparseSet vals, SparseSet vals2, int arity, int numValue) {
        restriction.clear();
        vars.clear();
        vars2.clear();
        vals.clear();
        vals2.clear();
        int addArity = arity + 1;
        for (int i = sccStartIndex, end = getSCCEndIndex(sccStartIndex); i <= end; i++) {
            restriction.set(dense[i]);
        }

        for (int i = restriction.nextSetBit(0); i != -1 && i < arity; i = restriction.nextSetBit(i + 1)) {
            vars.add(i);
            vars2.add(i);
        }

        for (int i = restriction.nextSetBit(addArity), ub = addArity + numValue; i != -1 && i < ub; i = restriction.nextSetBit(i + 1)) {
            vals.add(i - addArity);
            vals2.add(i - addArity);
        }
    }

    public void getPartitionBitSetMaskAndVars(int sccStartIndex, BitSet restriction, SparseSet vars, SparseSet vars2, SparseSet vals, SparseSet vals2, SparseSet vals3, int arity, int numValue) {
        restriction.clear();
        vars.clear();
        vars2.clear();
        vals.clear();
        vals2.clear();
        vals3.clear();
        int addArity = arity + 1;
        for (int i = sccStartIndex, end = getSCCEndIndex(sccStartIndex); i <= end; i++) {
            restriction.set(dense[i]);
        }

        for (int i = restriction.nextSetBit(0); i != -1 && i < arity; i = restriction.nextSetBit(i + 1)) {
            vars.add(i);
            vars2.add(i);
        }

        for (int i = restriction.nextSetBit(addArity), ub = addArity + numValue; i != -1 && i < ub; i = restriction.nextSetBit(i + 1)) {
            int a = i - addArity;
            vals.add(a);
            vals2.add(a);
            vals3.add(a);
        }
    }

    @Override
    public String toString() {
        StringBuilder ss = new StringBuilder("[");
        for (int i = 0; i < size; i++) {
            if (sccStartMask.get(i)) {
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
                .append(sccStartMask.toString());
        return ss.toString();
    }

    public NodeType getNodeType(int nodeIndex) {
        if (nodeIndex < numVars) {
            return NodeType.VAR;
        } else if (nodeIndex == numVars) {
            return NodeType.SINK;
        } else {
            return NodeType.VAL;
        }
    }

//    public PartitionIterator iterator(){}
//
//    public class PartitionIterator{
//        int partitionCursor;
//        public class SCCIterator{
//            int sccCursor;
//
//        }
//        public SCCIterator iterator(int sccStart){
//
//        }
//        public getValid(){
//
//        }
//    }

//    public class SCCIterator{
//        int cursor;
//        public SCCIterator(int pos, boolean isSCCStart=false){
//
//        }
//        public hasNextValid(){
//
//        }
//    }
}
