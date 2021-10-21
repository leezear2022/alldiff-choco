//package org.chocosolver.util.objects;
//
//import gnu.trove.set.hash.TIntHashSet;
//import org.chocosolver.memory.IEnvironment;
//import org.chocosolver.memory.IStateBitSet;
//
//import java.util.Arrays;
//import java.util.BitSet;
//
//public class RSetPartition2 {
//    int[] sccDense;
//    int[] sccSparse;
//    IStateBitSet sccStart;
//
//    int[] varDense;
//    int[] varSparse;
//    IStateBitSet varStart;
//
//    int[] valDense;
//    int[] valSparse;
//    IStateBitSet valStart;
//
//    IEnvironment env;
//    int limit = 0;
//    int varLimit = 0;
//    int valLimit = 0;
//    int iterIdx = -1;
//    int sccSize;
//    int varSize;
//    int valSize;
//    int lastPos;
//    int tmpStartIndex = -1;
//    int sinkIndex;
//
//    public RSetPartition2(int numVars, int numVals, IEnvironment e) {
//        this.sinkIndex = numVars + 1;
//        this.varSize = numVars;
//        this.valSize = numVals;
//        this.sccSize = sinkIndex + numVals;
//        this.lastPos = sccSize - 1;
//        this.env = e;
//        sccDense = new int[sccSize];
//        sccSparse = new int[sccSize];
//        for (int i = 0; i < sccSize; i++) {
//            sccDense[i] = i;
//            sccSparse[i] = i;
//        }
//
//        // 包括sink节点
//        varDense = new int[numVars+1];
//        varSparse = new int[numVars];
//        for (int i = 0; i < numVars; i++) {
//            varDense[i] = i;
//            varSparse[i] = i;
//        }
//
//        valDense = new int[numVals];
//        valSparse = new int[numVals];
//        for (int i = 0; i < numVals; i++) {
//            valDense[i] = i;
//            valSparse[i] = i;
//        }
//        // 1标记SCC的开头 i.e. 10001,00000
//        sccStart = env.makeBitSet(sccSize);
//        //splitPoint =
//        sccStart.set(0);
//
//        // 1标记SCC-var的开头 i.e. 10001,00000
//        varStart = env.makeBitSet(varSize);
//        //splitPoint = 10001,00000
//        varStart.set(0);
//
//        // 1标记SCC-val的开头 i.e. 10001,00000
//        valStart = env.makeBitSet(valSize);
//        //splitPoint = 10001,00000
//        valStart.set(0);
//    }
//
//    public void add(int e) {
////        System.out.println("limit: " + limit);
//        int index = sccSparse[e];
//        int tmp = sccDense[limit];
//        sccSparse[e] = limit;
//        sccSparse[tmp] = index;
//        sccDense[index] = tmp;
//        sccDense[limit] = e;
//        ++limit;
//    }
//
//    public void addVar(int e) {
//        int index = sccSparse[e];
//        int tmp = sccDense[limit];
//        sccSparse[e] = limit;
//        sccSparse[tmp] = index;
//        sccDense[index] = tmp;
//        sccDense[limit] = e;
//        ++limit;
//        add();
//    }
//
//    public void addVal(int e) {
//
//    }
//
//    public void reset() {
//        sccStart.clear();
//        limit = 0;
//        varStart.clear();
//        varLimit = 0;
//        valStart.clear();
//        valLimit = 0;
//    }
//
//    public void remove(int e) {
//        // 查找当前索引
//        int index = sccSparse[e];
//        // 查找边界索引
//        int index2 = getSCCEndIndex(index);
//        if (index != index2) {
//            int tmp = sccDense[index2];
//            sccSparse[e] = index2;
//            sccSparse[tmp] = index;
//            sccDense[index] = tmp;
//            sccDense[index2] = e;
//        }
//        // 前一处设置split
//        sccStart.clear(index2);
//    }
//
//    public int removeToTmp(int e) {
//        //若无临时区域
//        if (tmpStartIndex == -1) {
//            // 查找当前索引
//            int index = sccSparse[e];
//            // 查找边界索引
//            tmpStartIndex = getSCCEndIndex(index);
//            if (index != tmpStartIndex) {
//                int tmp = sccDense[tmpStartIndex];
//                sccSparse[e] = tmpStartIndex;
//                sccSparse[tmp] = index;
//                sccDense[index] = tmp;
//                sccDense[tmpStartIndex] = e;
//            }
//            // 前一处设置split
//            sccStart.clear(tmpStartIndex);
//        } else {
//            // 查找当前索引
//            int index = sccSparse[e];
//            tmpStartIndex--;
//            // 查找边界索引
//            if (index != tmpStartIndex) {
//                int tmp = sccDense[tmpStartIndex];
//                sccSparse[e] = tmpStartIndex;
//                sccSparse[tmp] = index;
//                sccDense[index] = tmp;
//                sccDense[tmpStartIndex] = e;
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
//
//    public void setSplit() {
//        // 若为0则表示新分区的开始
//        if (limit != size)
//            sccStart.clear(limit);
//    }
//
//    public int resetIteratorByElement(int e) {
//        iterIdx = getSCCStartIndex(sccSparse[e]);
//        return iterIdx;
//    }
//
//    public int resetLimitByElement(int e) {
//        limit = getSCCStartIndex(sccSparse[e]);
//        return limit;
//    }
//
//    public boolean hasNext() {
//        return iterIdx != size && sccStart.get(iterIdx);
//    }
//
//    public int next() {
//        return sccDense[iterIdx++];
//    }
//
//    public int getValue() {
//        return sccDense[iterIdx];
//    }
//
//    // iter go next and test valid;
//    public boolean nextValid() {
//        return ++iterIdx != size && sccStart.get(iterIdx);
//    }
//
//    private int getSCCEndIndex(int index) {
//        return index < lastPos ? sccStart.nextClearBit(index + 1) - 1 : lastPos;
//    }
//
//    private int getSCCStartIndex(int index) {
//        return sccStart.prevClearBit(index);
//    }
//
//    public int getSCCStartIndexByElement(int e) {
//        return getSCCStartIndex(sccSparse[e]);
//    }
//
//    public boolean inSameSCC(int a, int b) {
//        return getSCCStartIndexByElement(a) == getSCCStartIndexByElement(b);
//    }
//
//    public void setIteratorIndex(int iterIdx) {
//        this.iterIdx = iterIdx;
//    }
//
//    public boolean greatThanOne(int startIterIdx) {
//        return !sccStart.get(startIterIdx);
//    }
//
////    public boolean greatThanTwo(int startIterIdx) {
////        if (startIterIdx + 2 == size) {
////            // 正好是未尾两个元素
////            return !sccStart.get(startIterIdx + 1);
////        }else if (startIterIdx + 2 < size){
////            // 不是未尾两个元素
////            return !sccStart.get(startIterIdx)
////        }
////        return
////        else
////        return
////    }
//
//    public int partitionSize(int startIterIdx) {
//        return getSCCEndIndex(startIterIdx) - getSCCStartIndex(startIterIdx);
//    }
//
//    public boolean isSingleton(int varID) {
//        // 如果varID是0且它的后一个也是0 那么它是singleton的
//        int index = sccSparse[varID];
//        if (index == size) {
//            return !sccStart.get(index);
//        } else {
//            return !sccStart.get(index) && !sccStart.get(index + 1);
//        }
//    }
//
//    public void getSCCStartIndex(TIntHashSet indices) {
//        indices.clear();
//        for (int i = sccStart.nextClearBit(0); i < size; i = sccStart.nextClearBit(i + 1)) {
//            indices.add(i);
//        }
//    }
//
//    public void getPartitionVars(int sccStartIndex, SparseSet vars) {
////        restriction.clear();
//        vars.clear();
//        for (int i = sccStartIndex, end = getSCCEndIndex(sccStartIndex); i < end; i++) {
//            vars.add(i);
//        }
//    }
//
//    public void getPartitionBitSetMask(int sccStartIndex, BitSet restriction) {
//        restriction.clear();
//        for (int i = sccStartIndex, end = getSCCEndIndex(sccStartIndex); i < end; i++) {
//            restriction.set(sccDense[i]);
//        }
//    }
//
//    public void getPartitionBitSetMaskAndVars(int sccStartIndex, BitSet restriction, SparseSet vars, SparseSet vals, int arity, int numValue) {
//        restriction.clear();
//        vars.clear();
//        vals.clear();
//        int addArity = arity + 1;
//        for (int i = sccStartIndex, end = getSCCEndIndex(sccStartIndex); i <= end; i++) {
//            int valIdx = sccDense[i];
//            restriction.set(valIdx);
//        }
//
//        for (int i = restriction.nextSetBit(0); i != -1 && i < arity; i = restriction.nextSetBit(i + 1)) {
//            vars.add(i);
//        }
//
//        for (int i = restriction.nextSetBit(addArity), ub = addArity + numValue; i != -1 && i < ub; i = restriction.nextSetBit(i + 1)) {
//            vals.add(i - addArity);
//        }
//    }
//
//    public void getPartitionBitSetMaskAndVars(int sccStartIndex, BitSet restriction, SparseSet vars, SparseSet vars2, SparseSet vals, SparseSet vals2, int arity, int numValue) {
//        restriction.clear();
//        vars.clear();
//        vars2.clear();
//        vals.clear();
//        vals2.clear();
//        int addArity = arity + 1;
//        for (int i = sccStartIndex, end = getSCCEndIndex(sccStartIndex); i <= end; i++) {
//            restriction.set(sccDense[i]);
//        }
//
//        for (int i = restriction.nextSetBit(0); i != -1 && i < arity; i = restriction.nextSetBit(i + 1)) {
//            vars.add(i);
//            vars2.add(i);
//        }
//
//        for (int i = restriction.nextSetBit(addArity), ub = addArity + numValue; i != -1 && i < ub; i = restriction.nextSetBit(i + 1)) {
//            vals.add(i - addArity);
//            vals2.add(i - addArity);
//        }
//    }
//
//    public void getPartitionBitSetMaskAndVars(int sccStartIndex, BitSet restriction, SparseSet vars, SparseSet vars2, SparseSet vals, SparseSet vals2, SparseSet vals3, int arity, int numValue) {
//        restriction.clear();
//        vars.clear();
//        vars2.clear();
//        vals.clear();
//        vals2.clear();
//        vals3.clear();
//        int addArity = arity + 1;
//        for (int i = sccStartIndex, end = getSCCEndIndex(sccStartIndex); i <= end; i++) {
//            restriction.set(sccDense[i]);
//        }
//
//        for (int i = restriction.nextSetBit(0); i != -1 && i < arity; i = restriction.nextSetBit(i + 1)) {
//            vars.add(i);
//            vars2.add(i);
//        }
//
//        for (int i = restriction.nextSetBit(addArity), ub = addArity + numValue; i != -1 && i < ub; i = restriction.nextSetBit(i + 1)) {
//            int a = i - addArity;
//            vals.add(a);
//            vals2.add(a);
//            vals3.add(a);
//        }
//    }
//
//    @Override
//    public String toString() {
//        StringBuilder ss = new StringBuilder("[");
//        for (int i = 0; i < size; i++) {
//            if (sccStart.get(i)) {
//                ss.append(sccDense[i]).append(" ");
//            } else {
//                ss.append("| ").append(sccDense[i]).append(" ");
//            }
//        }
//
//        ss.append("] ")
//                .append("dense: ")
//                .append(Arrays.toString(sccDense))
//                .append(", sparse: ")
//                .append(Arrays.toString(sccSparse))
//                .append(", split:")
//                .append(sccStart.toString());
//        return ss.toString();
//    }
//
//    public VarIterator varIterator(int varIdx) {
//        return
//    }
//
//    public class VarIterator {
//        int curror = -1;
//
//        public VarIterator(int varIdx) {
//
//        }
//
//        public int next() {
//
//        }
//
//        public boolean hasNext() {
//
//        }
//    }
//
//    public class ValIterator {
//
//    }
//
//    public class SCCIterator {
//
//    }
//}
