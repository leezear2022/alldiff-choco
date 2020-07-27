package org.chocosolver.util.objects;

//import jdk.internal.vm.annotation.ForceInline;

/**
 * Implementation based on "2013_TRICS_Sparse-Sets for Domain Implementation".
 * <p/>
 * <p/>
 * Created by Jia'nan Chen on 13/11/2019.
 * Project: choco.
 */


// 分别为bind区|有效值区|无效值区
public class NaiveSparseSet {
    private int length;
    private int[] sparse;
    private int[] dense;
    //limit 是不包括本值之前的值有效
    private int[] limit;
    //    private TIntArrayList limit;
    private int lastLimit;
    // 用于遍历有效部分或无效部分
//    private int iterator;
    // 用于记住原limit
//    private int oldLimit;
//    private int iterator2;
    public static int INDEX_OVERFLOW = -1;
    private static int NUM_MARKS = 6;
    private int lastLevel;

    private int[] mark;
    private int bindPos = 0;
    private int lastPos = 0;

    public NaiveSparseSet(int length) {
        this.length = length;
        this.mark = new int[NUM_MARKS];
        this.sparse = new int[length];
        this.dense = new int[length];
        this.limit = new int[length];

        for (int i = 0; i < length; i++) {
            this.sparse[i] = i;
            this.dense[i] = i;
            this.limit[i] = INDEX_OVERFLOW;
        }
        this.limit[lastPos] = length;
    }

    public void reserve(int length) {
        this.length = length;
        this.sparse = null;
        this.dense = null;
        this.sparse = new int[length];
        this.dense = new int[length];

        for (int i = 0; i < length; i++) {
            this.sparse[i] = i;
            this.dense[i] = i;
            this.limit[i] = -1;
        }

        this.lastPos = 0;
        this.limit[lastPos] = length;
    }

    public int newLevel() {
        limit[++lastPos] = limit[lastPos];
        return lastPos;
    }

    public int deleteLevel() {
        limit[lastPos--] = -1;
        return lastPos;
    }

    //    public void fill() {
//        limit. = length - 1;
//    }
//
    public void clear() {
        while (lastPos != 0) {
            limit[--lastPos] = -1;
        }
        bindPos = 0;
    }

    public boolean isValidAtLevel(int e, int level) {
        return sparse[e] < limit[level];
    }

    public boolean isValid(int e) {
        return sparse[e] < limit[lastPos];
    }

//    @ForceInline
//    public boolean isBind(int e, int level) {
//        return sparse[e] < limit[level];
//    }

    public boolean isBind(int e) {
        return sparse[e] < bindPos;
    }

    private void remove(int e) {
        if (isValid(e)) {
            swap(dense[e], limit[lastPos] - 1);
            --limit[lastPos];
        }
    }

    public void add(int e) {
        if (!isValid(e)) {
            swap(dense[e], limit[lastPos]);
            ++limit[lastPos];
        }
    }

    public void bind(int e) {
        if (isValid(e)) {
            swap(dense[e], bindPos);
            ++bindPos;
        }
    }

    private void swap(int i, int j) {
        int tmp = dense[i];
        dense[i] = dense[j];
        dense[j] = tmp;
        sparse[dense[i]] = i;
        sparse[dense[j]] = j;
    }

    public Iterator begin() {
        return new Iterator();
    }

    class Iterator {
        int index = 0;

    }
//
//    // 遍历有效部分（左部集合）
//    public void iterateValid() {
//        iterator = -1;
//    }
//
//    // 从某个值起，遍历有效部分（左部集合）
//    public void iterateValid(int e) {
//        iterator = sparse[e];
//    }
//
//    public boolean hasNextValid() {
//        return iterator + 1 <= limit;
//    }
//
//    // 遍历无效部分（右部集合）
//    public void iterateInvalid() {
//        iterator = limit;
//    }
//
//    public boolean hasNextInvalid() {
//        return iterator + 1 < length;
//    }
//
//    public int next() {
//        return dense[++iterator];
//    }
//
//    public int current() {
//        return dense[iterator];
//    }
//
//    // 只能用于在迭代过程中删除上一个迭代元素
//    public void remove() {
//        if (iterator == -1) {
//            return;
//        }
//        int e1 = dense[iterator];
//        int e2 = dense[limit];
//        dense[iterator] = e2;
//        dense[limit] = e1;
//        sparse[e1] = limit;
//        sparse[e2] = iterator;
//        limit--;
//        iterator--;
//    }
//
//
//    public void record() {
//        oldLimit = limit;
//    }
//
//    public void restore() {
//        limit = oldLimit;
//    }
//
//
//    // 遍历limit到oldLimit之间的集合
//    public void iterateLimit() {
//        iterator2 = limit;
//    }
//
//    // 只能用于在迭代过程中添加上一个迭代元素
//    public void addLimit() {
//        if (iterator2 == length) {
//            return;
//        }
//        limit++;
//        iterator2++;
//        int e1 = dense[iterator2];
//        int e2 = dense[limit];
//        dense[iterator2] = e2;
//        dense[limit] = e1;
//        sparse[e1] = limit;
//        sparse[e2] = iterator2;
//    }
//
//    public int nextLimit() {
//        return dense[++iterator2];
//    }
//
//    public boolean hasNextLimit() {
//        return iterator2 + 1 <= oldLimit;
//    }

    @Override
    public String toString() {
        StringBuilder s = new StringBuilder();
        s.append("dense  = {");
        for (int i = 0; i < sparse.length; i++) {
            if (i == 0) {
                s.append(dense[i]);
            } else {
                s.append(", ").append(dense[i]);
            }
        }
        s.append("}\n");
        s.append("sparse = {");
        for (int i = 0; i < sparse.length; i++) {
            if (i == 0) {
                s.append(sparse[i]);
            } else {
                s.append(", ").append(sparse[i]);
            }
        }
        s.append("}\nlimit = ").append(limit);
        return s.toString();
    }
}
