package org.chocosolver.util.objects;


public class NaiveBitSet {

    protected long[] words;
    protected int longSize;
    protected int bitSize;
    protected int limit;
    protected long lastMask;

    protected final static int ADDRESS_BITS_PER_WORD = 6;
    protected final static int BITS_PER_WORD = 1 << ADDRESS_BITS_PER_WORD;
    protected final static int BIT_INDEX_MASK = BITS_PER_WORD - 1;
    /* Used to shift left or right for a partial word mask */
    protected static final long WORD_MASK = 0xffffffffffffffffL;
    protected static final long MOD_MASK = 0x3fL;
    protected static final int MOD_MASK_INT = 0x3f;

    public NaiveBitSet(int nbits) {
        this.bitSize = nbits;
        longSize = wordIndex(nbits - 1) + 1;
        this.limit = nbits % BITS_PER_WORD;
        this.lastMask = WORD_MASK >>> (BITS_PER_WORD - limit);
        this.words = new long[longSize];
    }

    protected static int wordIndex(int bitIndex) {
        return bitIndex >> ADDRESS_BITS_PER_WORD;
    }

    protected static int wordOffset(int bitIndex) {
        return bitIndex & MOD_MASK_INT;
    }

    public int longSize() {
        return longSize;
    }

    public int bitSize() {
        return bitSize;
    }

    public void flip() {
        for (int i = 0; i < longSize; ++i) {
            words[i] = ~words[i];
        }
        words[longSize - 1] &= lastMask;
    }

    public void set(int bitIndex) {
        this.words[wordIndex(bitIndex)] |= 1L << bitIndex;
    }

    public void set(NaiveBitSet s) {
        for (int i = 0; i < longSize; ++i) {
            this.words[i] = s.words[i];
        }
    }

    public void set(int startIndex, NaiveBitSet b) {
//        for(int i = wordIndex(startIndex);)
    }

    public void naiveSet(int s, NaiveBitSet nbs) {
        int a = wordIndex(s);
        int b = wordOffset(s);
        // 先确定怎么偏移
        if (nbs.longSize == 1) {
            // 即 nbs.longSize =1
            if ((b + nbs.bitSize) < BITS_PER_WORD) {
                // 如果偏移量和整个bitset长度相加之后仍小于64，直接做
                // 取反码
                // long rmask = (WORD_MASK << (nbs.bitSize - b)) | (WORD_MASK >>> (BITS_PER_WORD - b));
                // 取掩码, 先左移取反再左移，移之后是：111...10..01...11这样的形式
//                long rMask = (~(~(WORD_MASK << nbs.bitSize) << b));
                this.words[a] = this.words[a] & (~(~(WORD_MASK << nbs.bitSize) << b)) | (nbs.words[0] << b);
            } else {
                int offset = (BITS_PER_WORD << 1) - nbs.bitSize - b;
                // 如果偏移量和整个bitset长度相加之后仍大于等于64，则需要用到this.words的下一个
                this.words[a] = ((~(WORD_MASK << b)) & this.words[a]) | (nbs.words[0] << b);
                this.words[a + 1] = (this.words[a + 1] & (~(WORD_MASK >> offset))) | (nbs.words[0] >> offset);
            }
        } else {
            int endIndex = s + nbs.bitSize;
            int c = wordIndex(endIndex);
            int d = wordOffset(endIndex);
//            int offset1 = nbs.bitSize + s - BITS_PER_WORD;
            int offset = (BITS_PER_WORD << 1) - nbs.bitSize - b;
            // 先不计算最后一个影响位
            for (int i = 0, len = c - 1; i < len; ++i) {
                int j = a + i;
                this.words[j] = ((~(WORD_MASK << s)) & this.words[j]) | (nbs.words[i] << s);
                this.words[j + 1] = (this.words[j + 1] & (~(WORD_MASK >> offset))) | (nbs.words[i] >> offset);
            }
        }
//        for (int i = 0, len = s.longSize; i < len; ++i) {
//            int j = b + i;
//            // 清空this中待设定的的部分，
//            // 一般要操作两个相邻的 this.words
//            // 先
//            this.words[j] = ((~(WORD_MASK << a) & this.words[a]) | (s.words[0] << a));
//            this.words[j + 1] = ((WORD_MASK << a) & this.words[j + 1]) | (s.words[0] >> BITS_PER_WORD - a);
//
////            this.words[j] = ~((s.words[i] << startBitIndex) ^ (WORD_MASK << startBitIndex));
////            this.words[j + 1] &=
////                    pre = s.words[i] << startBitIndex;
////            next = s.words[i] & (WORD_MASK >> startBitIndex);
//
//        }
    }

    public void naiveAnd(int s, NaiveBitSet nbs) {
        int a = wordIndex(s);
        int b = wordOffset(s);
        // 先确定怎么偏移
        if (nbs.longSize == 1) {
            // 即 nbs.longSize =1
            if ((b + nbs.bitSize) < BITS_PER_WORD) {
                // 如果偏移量和整个bitset长度相加之后仍小于64，直接做
                // 掩码，先让开nbs的长度，装入nbs，再移动b的长度，装入填充
                this.words[a] &= ((WORD_MASK << nbs.bitSize) | nbs.words[0]) << b | (~(WORD_MASK << b));
            } else {
//                int offset1 = nbs.bitSize + b - BITS_PER_WORD;
//                int offset2 = BITS_PER_WORD - offset1;
                int offset = (BITS_PER_WORD << 1) - nbs.bitSize - b;
                // 如果偏移量和整个bitset长度相加之后仍大于等于64，则需要用到this.words的下一个
                this.words[a] &= (~(WORD_MASK << b)) | (nbs.words[0] << b);
//                this.words[a + 1] &= (WORD_MASK << offset1) | (nbs.words[0] >> offset2);
                this.words[a + 1] &= (~(WORD_MASK >> offset)) | (nbs.words[0] >> offset);
            }
        } else {
            int endIndex = s + nbs.bitSize;
            int c = wordIndex(endIndex);
            int d = wordOffset(endIndex);
//            int offset1 = nbs.bitSize + s - BITS_PER_WORD;
            int offset = (BITS_PER_WORD << 1) - nbs.bitSize - b;
            // 先不计算最后一个影响位
            for (int i = 0, len = c - 1; i < len; ++i) {
                int j = a + i;
                this.words[j] &= (~(WORD_MASK << s)) | (nbs.words[i] << s);
                this.words[j + 1] &= (~(WORD_MASK >> offset)) | (nbs.words[i] >> offset);
            }
        }
    }


    public void clear() {
        for (int i = 0; i < longSize; ++i) {
            this.words[i] = 0L;
        }
    }

    public void set() {
        int len = longSize - 1;
        for (int i = 0; i < len; ++i) {
            this.words[i] = WORD_MASK;
        }
        this.words[len] = lastMask;
    }

    public void clear(int bitIndex) {
        this.words[wordIndex(bitIndex)] &= ~(1L << bitIndex);
    }

    // 从本集合中移除s中的元素
    public void clear(NaiveBitSet s) {
        for (int i = 0; i < longSize; ++i) {
            this.words[i] &= ~s.words[i];
        }
    }

    // 从本集合中移除s中的元素
    public void clear(NaiveSparseBitSet s) {
        for (int i = 0, len = s.longSize; i < len; ++i) {
            this.words[s.index[i]] &= ~s.words[i];
        }
    }

    public void clearAfterAnd(NaiveSparseBitSet a, NaiveBitSet b) {
        for (int i = 0, len = a.longSize; i < len; ++i) {
            int offset = a.index[i];
            this.words[offset] &= ~(a.words[i] & b.words[offset]);
        }
    }

    public boolean isEmpty() {
        for (int i = 0; i < longSize; ++i) {
            if (this.words[i] != 0L) {
                return false;
            }
        }
        return true;
    }

    public boolean get(int bitIndex) {
        int wordIndex = wordIndex(bitIndex);
        return wordIndex < longSize && (this.words[wordIndex] & 1L << bitIndex) != 0L;

    }

    public void and(NaiveBitSet s) {
        for (int i = 0; i < longSize; ++i) {
            this.words[i] &= s.words[i];
        }
    }

    public void or(NaiveBitSet s) {
        for (int i = 0; i < longSize; ++i) {
            this.words[i] |= s.words[i];
        }
    }


    public void setThenAnd(NaiveSparseBitSet a, NaiveBitSet b) {
        for (int i = 0, len = a.longSize; i < len; ++i) {
            int offset = a.index[i];
            this.words[offset] |= a.words[i] & b.words[offset];
        }
    }

    public void setThenAnd(LargeBitSet a, NaiveBitSet b) {
        for (int i = 0, len = a.limit; i < len; ++i) {
            int offset = a.dense[i];
            this.words[offset] |= a.words[i] & b.words[offset];
        }
    }

    // 判断两个集合是否有交集
    // 如果有，返回第一个相交的值
    // 如果没有，返回-1
    public int isIntersect(NaiveBitSet s) {
        long word;
        for (int i = 0; i < longSize; ++i) {
            word = this.words[i] & s.words[i];
            if (word != 0L) {
                return i * 64 + Long.numberOfTrailingZeros(word);
            }
        }
        return -1;
    }

    // 判断两个集合是否有交集
    // 如果有，返回第一个相交的值
    // 如果没有，返回-1
    public boolean isIntersect(LargeBitSet s) {
        long word;
        for (int i = 0; i < s.limit; ++i) {
            int offset = s.dense[i];
            if ((this.words[offset] & s.words[i]) != 0L) {
                return true;
            }
        }
        return false;
    }

    // 判断两个集合是否有交集
    public boolean isIntersect(NaiveSparseBitSet s) {
        for (int i = 0, len = s.longSize; i < len; ++i) {
            if ((this.words[s.index[i]] & s.words[i]) != 0L) {
                return true;
            }
        }
        return false;
    }

    public int nextSetBit(int fromIndex) {
        if (fromIndex < 0) {
            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        } else {
            int u = wordIndex(fromIndex);
            if (u >= this.longSize) {
                return -1;
            } else {
                long word;
                for (word = this.words[u] & -1L << fromIndex; word == 0L; word = this.words[u]) {
                    ++u;
                    if (u == this.longSize) {
                        return -1;
                    }
                }

                return u * 64 + Long.numberOfTrailingZeros(word);
            }
        }
    }

    public int nextClearBit(int fromIndex) {
        // Neither spec nor implementation handle bitsets of maximal length.
        // See 4816253.
        if (fromIndex < 0)
            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);


        int u = wordIndex(fromIndex);
        if (u >= longSize)
            return fromIndex;

        long word = ~words[u] & (WORD_MASK << fromIndex);

        while (true) {
            if (word != 0)
                return (u * BITS_PER_WORD) + Long.numberOfTrailingZeros(word);
            if (++u == longSize)
                return longSize * BITS_PER_WORD;
            word = ~words[u];
        }
    }

    public int capacity() {
        int sum = 0;
        for (int i = 0; i < longSize; ++i)
            sum += Long.bitCount(words[i]);
        return sum;
    }

    public int size() {
        int sum = 0;
        for (int i = 0; i < longSize; ++i)
            sum += Long.bitCount(words[i]);
        return sum;
    }

    @Override
    public String toString() {

        final int MAX_INITIAL_CAPACITY = Integer.MAX_VALUE - 8;
        int numBits = longSize * BITS_PER_WORD;
        // Avoid overflow in the case of a humongous numBits
        int initialCapacity = (numBits <= (MAX_INITIAL_CAPACITY - 2) / 6) ?
                6 * numBits + 2 : MAX_INITIAL_CAPACITY;
        StringBuilder b = new StringBuilder(initialCapacity);
        b.append('{');

        int i = nextSetBit(0);
        if (i != -1) {
            b.append(i);
            while (true) {
                if (++i < 0) break;
                if ((i = nextSetBit(i)) < 0) break;
                int endOfRun = nextClearBit(i);
                do {
                    b.append(", ").append(i);
                }
                while (++i != endOfRun);
            }
        }

        b.append('}');
        return b.toString();
    }

    public void and(NaiveBitSet a, NaiveBitSet b) {
        for (int i = 0; i < this.longSize; ++i) {
            this.words[i] &= (a.words[i] & b.words[i]);
        }
    }

    public void and(NaiveBitSet a, NaiveBitSet b, NaiveBitSet c, NaiveBitSet d) {
        for (int i = 0, len = longSize; i < len; ++i) {
            this.words[i] = a.words[i] & b.words[i] & c.words[i] & d.words[i];
        }
    }

    public final static void and(NaiveBitSet res, NaiveBitSet a, NaiveBitSet b) {
        for (int i = 0, len = res.longSize; i < len; ++i) {
            res.words[i] = a.words[i] & b.words[i];
        }
    }

    public final static void and(NaiveBitSet res, NaiveBitSet a, NaiveBitSet b, NaiveBitSet c, NaiveBitSet d) {
        for (int i = 0, len = res.longSize; i < len; ++i) {
            res.words[i] = a.words[i] & b.words[i] & c.words[i] & d.words[i];
        }
    }

    public final static boolean EmptyAnd(NaiveBitSet a, NaiveBitSet b) {
        for (int i = 0; i < a.longSize; ++i) {
            if ((a.words[i] & b.words[i]) != 0L) {
                return false;
            }
        }
        return true;
    }

    public void or(NaiveSparseBitSet s) {
        //以较小的s为区间
        for (int i = 0, len = s.longSize; i < len; ++i) {
            int offset = s.index[i];
            this.words[offset] |= s.words[i];
        }
    }

    // 先或再检查为空
    public boolean orCheckEmpty(NaiveSparseBitSet s) {
        //以较小的s为区间
        for (int i = 0, len = s.longSize; i < len; ++i) {
            int offset = s.index[i];
            this.words[offset] |= s.words[i];
            if (this.words[offset] != 0L) {
                return false;
            }
        }
        return true;
    }

    // 只尝试检查或的结果不改值
    public boolean orTestEmpty(NaiveSparseBitSet s) {
        //以较小的s为区间
//        boolean res = false;
        for (int i = 0, len = s.longSize; i < len; ++i) {
            int offset = s.index[i];
            if ((this.words[offset] | s.words[i]) != 0L) {
                return false;
            }
        }
        return true;
    }

    // 只尝试检查或的结果不改值
    public boolean tryAndEmpty(NaiveSparseBitSet s) {
        //以较小的s为区间
        for (int i = 0, len = s.longSize; i < len; ++i) {
            int offset = s.index[i];
            if ((this.words[offset] & s.words[i]) != 0L) {
                return false;
            }
        }
        return true;
    }


    public final static boolean EmptyAnd(NaiveBitSet a, NaiveBitSet b, NaiveBitSet c, NaiveBitSet d) {
        for (int i = 0; i < a.longSize; ++i) {
            if ((a.words[i] & b.words[i] & c.words[i] & d.words[i]) != 0L) {
                return false;
            }
        }
        return true;
    }

    public final static int NextSetBitAfterMinus(NaiveBitSet a, NaiveBitSet b, int fromIndex) {
        if (fromIndex < 0) {
            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        } else {
            int u = a.wordIndex(fromIndex);
            if (u >= a.longSize) {
                return -1;
            } else {
                long word;
                for (word = a.words[u] & (~b.words[u]) & -1L << fromIndex; word == 0L; word = (a.words[u] & (~b.words[u]))) {
                    ++u;
                    if (u == a.longSize) {
                        return -1;
                    }
                }

                return u * 64 + Long.numberOfTrailingZeros(word);
            }
        }
    }


    // 从a中除去b，再加入现在的值
    public void orAfterMinus(NaiveBitSet a, NaiveBitSet b) {
        for (int i = 0; i < longSize; ++i) {
            this.words[i] |= a.words[i] & ~b.words[i];
        }
    }

    // 从a中除去b
    public void setAfterMinus(NaiveBitSet a, NaiveBitSet b) {
        for (int i = 0; i < longSize; ++i) {
            this.words[i] = a.words[i] & ~b.words[i];
        }
    }

    // a和b共同部分
    public void setAfterAnd(NaiveBitSet a, NaiveBitSet b) {
        for (int i = 0; i < longSize; ++i) {
            this.words[i] = a.words[i] & b.words[i];
        }
    }

    // 与a取反
    public void andAfterNot(NaiveBitSet a) {
        for (int i = 0; i < longSize; ++i) {
            this.words[i] = ~a.words[i];
        }
    }

//    public void orAfterAnd(NaiveSparseBitSet a, NaiveSparseBitSet b) {
//        int min;
//        //以短
//        if (a.longSize > b.longSize) {
//
//        }
//
//    }
}
