package org.chocosolver.util.objects;


import java.util.Arrays;
import java.util.Map;
import java.util.TreeMap;

public class NaiveSparseBitSet {
    // 用于and运算的mask外侧环以1
//    long[] andMask;
    // 用于or运算的mask外侧环以0
//    long[] orMask;
    protected int[] index;
    protected long[] words;
    int startIndex;
    int endIndex;
    //    int minIndex = Integer.MAX_VALUE;
//    int maxIndex = Integer.MIN_VALUE;
    //    private ArrayList<Integer> tmpList = new ArrayList<>();
    private Map<Integer, Long> tmp = new TreeMap<>();

    //    int bitSize;
    protected int longSize;

    protected final static int ADDRESS_BITS_PER_WORD = 6;
    protected final static int BITS_PER_WORD = 1 << ADDRESS_BITS_PER_WORD;
    protected final static int BIT_INDEX_MASK = BITS_PER_WORD - 1;
    /* Used to shift left or right for a partial word mask */
    protected static final long WORD_MASK = 0xffffffffffffffffL;
    protected static final long MOD_MASK = 0x3fL;
    protected static final int MOD_MASK_INT = 0x3f;

    public NaiveSparseBitSet() {
        this.startIndex = 0;
    }

    public NaiveSparseBitSet(int s) {
        startIndex = s;
    }

    public void add(int a) {
//        tmpList.add(a);
        // 获取最大最小值
//        minIndex = Integer.min(a, minIndex);
//        maxIndex = Integer.max(a, maxIndex);
        // 拿到新地址
        int pos = startIndex + a;
        int k = wordIndex(pos);
        int v = wordOffset(pos);
        if (!tmp.containsKey(k)) {
            // 没有这个k就加一个新Key进去，并初始化数据
            tmp.put(k, 1L << v);
        } else {
            // 有就在原位置上修改这个值
            tmp.put(k, tmp.get(k) | (1L << v));
        }
    }

    public void addIndex(int pos) {
//        tmpList.add(a);
        // 获取最大最小值
//        minIndex = Integer.min(a, minIndex);
//        maxIndex = Integer.max(a, maxIndex);
        // 拿到新地址
        int k = wordIndex(pos);
        int v = wordOffset(pos);
        if (!tmp.containsKey(k)) {
            // 没有这个k就加一个新Key进去，并初始化数据
            tmp.put(k, 1L << v);
        } else {
            // 有就在原位置上修改这个值
            tmp.put(k, tmp.get(k) | (1L << v));
        }
    }

    // 集合类转数组
    public void complete() {
        this.longSize = this.tmp.size();
        this.index = new int[longSize];
        this.words = new long[longSize];
        int i = 0;

        for (Map.Entry<Integer, Long> entry : this.tmp.entrySet()) {
            this.index[i] = entry.getKey();
            this.words[i] = entry.getValue();
            ++i;
        }
        // 清除临时数据结构
        this.tmp.clear();
        this.tmp = null;
    }

//    public void set(int a) {
//        int pos = startIndex + a;
//        int k = wordIndex(pos);
//        int v = wordOffset(pos);
//        int i = Arrays.binarySearch(index, k);
//        words[i] |= 1L << v;
//    }

    public void set(int pos) {
        int k = wordIndex(pos);
        int v = wordOffset(pos);
        int i = Arrays.binarySearch(index, k);
        this.words[i] |= 1L << v;
    }

    public void clear() {
        for (int i = 0; i < longSize; ++i) {
            this.words[i] = 0L;
        }
    }

    public void and(NaiveBitSet s) {
        for (int i = 0; i < longSize; ++i) {
            int offset = this.index[i];
            this.words[i] &= s.words[offset];
        }
    }

    public void clear(int pos) {
        int k = wordIndex(pos);
        int v = wordOffset(pos);
        int i = Arrays.binarySearch(index, k);
        this.words[i] &= ~(1L << v);
    }

    protected static int wordIndex(int bitIndex) {
        return bitIndex >> ADDRESS_BITS_PER_WORD;
    }

    protected static int wordOffset(int bitIndex) {
        return bitIndex & MOD_MASK_INT;
    }

    @Override
    public String toString() {
        return super.toString();
    }
}

