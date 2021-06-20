package org.chocosolver.util.objects;

/**
 * Implementation based on "2013_TRICS_Sparse-Sets for Domain Implementation".
 * <p/>
 * <p/>
 * Created by Jia'nan Chen on 13/11/2019.
 * Project: choco.
 */

public class SparseSet {
    private int length;
    private int[] sparse;
    private int[] dense;
    private int limit;
    // 用于遍历有效部分或无效部分
    private int iterator;
    // 用于记住原limit
    private int oldLimit;
    private int iterator2;
//    private capacity

    public SparseSet(int length) {
        this.length = length;
        this.sparse = new int[length];
        this.dense = new int[length];
        for (int i = 0; i < length; i++) {
            this.sparse[i] = i;
            this.dense[i] = i;
        }
        this.limit = length - 1;
        this.oldLimit = limit;
        this.iterator = -1;
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
        }
        this.limit = length - 1;
        this.oldLimit = limit;
        this.iterator = -1;
    }

    public void fill() {
        limit = length - 1;
    }

    public void clear() {
        limit = -1;
    }

    public boolean contain(int e) {
        return sparse[e] <= limit;
    }

    public boolean empty() {
        return limit == -1;
    }

    public void remove(int e) {
        int index = sparse[e];
        if (index <= limit) {
            int tmp = dense[limit];
            sparse[e] = limit;
            sparse[tmp] = index;
            dense[index] = tmp;
            dense[limit] = e;
            limit--;
        }
    }

    public void add(int e) {
        int index = sparse[e];
        if (index > limit) {
            limit++;
            int tmp = dense[limit];
            sparse[e] = limit;
            sparse[tmp] = index;
            dense[index] = tmp;
            dense[limit] = e;
        }
    }

    // 遍历有效部分（左部集合）
    public void iterateValid() {
        iterator = -1;
    }

    // 从某个值起，遍历有效部分（左部集合）
    public void iterateValid(int e) {
        iterator = sparse[e];
    }

    public boolean hasNextValid() {
        return iterator + 1 <= limit;
    }

    // 遍历无效部分（右部集合）
    public void iterateInvalid() {
        iterator = limit;
    }

    public boolean hasNextInvalid() {
        return iterator + 1 < length;
    }

    public int next() {
        return dense[++iterator];
    }

    public int current() {
        return dense[iterator];
    }

    // 只能用于在迭代过程中删除上一个迭代元素
    public void remove() {
        if (iterator == -1) {
            return;
        }
        int e1 = dense[iterator];
        int e2 = dense[limit];
        dense[iterator] = e2;
        dense[limit] = e1;
        sparse[e1] = limit;
        sparse[e2] = iterator;
        limit--;
        iterator--;
    }


    public void record() {
        oldLimit = limit;
    }

    public void restore() {
        limit = oldLimit;
    }


    // 遍历limit到oldLimit之间的集合
    public void iterateLimit() {
        iterator2 = limit;
    }

    // 只能用于在迭代过程中添加上一个迭代元素
    public void addLimit() {
        if (iterator2 == length) {
            return;
        }
        limit++;
        iterator2++;
        int e1 = dense[iterator2];
        int e2 = dense[limit];
        dense[iterator2] = e2;
        dense[limit] = e1;
        sparse[e1] = limit;
        sparse[e2] = iterator2;
    }

    public int nextLimit() {
        return dense[++iterator2];
    }

    public boolean hasNextLimit() {
        return iterator2 + 1 <= oldLimit;
    }

    @Override
    public String toString() {
        StringBuilder s = new StringBuilder();
//        s.append("dense  = {");
//        for (int i = 0; i < sparse.length; i++) {
//            if (i == 0) {
//                s.append(dense[i]);
//            } else {
//                s.append(", ").append(dense[i]);
//            }
//        }
//        s.append("}\n");
//        s.append("sparse = {");
//        for (int i = 0; i < sparse.length; i++) {
//            if (i == 0) {
//                s.append(sparse[i]);
//            } else {
//                s.append(", ").append(sparse[i]);
//            }
//        }
//        s.append("}\nlimit = ").append(limit);
        for (int i = 0; i <= limit; i++) {
            s.append(dense[i]).append(" ");
        }
        return s.toString();
    }

    int[] toArray() {
        int[] arr = new int[limit + 1];
        for (int i = 0; i <= limit; i++) {
            arr[i] = dense[i];
        }
        return arr;
    }
}
