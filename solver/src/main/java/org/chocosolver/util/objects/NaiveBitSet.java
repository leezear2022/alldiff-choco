package org.chocosolver.util.objects;

import org.chocosolver.memory.IStateBitSet;

public class NaiveBitSet implements INaiveBitSet {

    protected long[] words;
    protected int longSize;
    protected int bitSize;
    protected int limit;
    protected long lastMask;
    protected int lowerIndex = longSize;
    protected int upperIndex = INDEX_OVERFLOW;
    protected int numBits = 0;

    protected final static int ADDRESS_BITS_PER_WORD = 6;
    protected final static int BITS_PER_WORD = 1 << ADDRESS_BITS_PER_WORD;
    protected final static int BIT_INDEX_MASK = BITS_PER_WORD - 1;
    /* Used to shift left or right for a partial word mask */
    protected static final long WORD_MASK = 0xffffffffffffffffL;
    protected static final long MOD_MASK = 0x3fL;
    protected static final int MOD_MASK_INT = 0x3f;
    protected static final int INDEX_OVERFLOW = -1;

    protected static int wordIndex(int bitIndex) {
        return bitIndex >> ADDRESS_BITS_PER_WORD;
    }


    protected static int wordOffset(int bitIndex) {
        return bitIndex & MOD_MASK_INT;
    }

    public NaiveBitSet(int nbits, boolean initValue) {
        this.bitSize = nbits;
        longSize = wordIndex(nbits - 1) + 1;
        limit = nbits % BITS_PER_WORD;
        lastMask = WORD_MASK >>> (BITS_PER_WORD - limit);
        words = new long[longSize];
        lowerIndex = longSize;
        upperIndex = INDEX_OVERFLOW;
        if (initValue) {
            set();
            numBits = nbits;
        }
    }

    @Override
    public void set() {
        int len = longSize - 1;
        for (int i = 0; i < len; ++i) {
            words[i] = WORD_MASK;
        }
        words[len] = lastMask;
        lowerIndex = 0;
        upperIndex = len;
        numBits = bitSize;
    }

    @Override
    public void set(int bitIdx) {
        int idx = wordIndex(bitIdx);
        // 原来是0 现在设置成1 unChanged = get(bitIdx) = false
        boolean unChanged = idx < longSize && (words[idx] & 1L << bitIdx) != 0L;

        if (!unChanged) {
            words[idx] |= 1L << bitIdx;

            if (idx < lowerIndex) {
                lowerIndex = idx;
            }

            if (idx > upperIndex) {
                upperIndex = idx;
            }

            numBits++;
        }
    }

    @Override
    public void set(INaiveBitSet s) {
        for (int i = 0; i < longSize; i++) {
            words[i] = s.getWord(i);
        }
        lowerIndex = s.firstSetIndex();
        upperIndex = s.lastSetIndex();
        numBits = s.size();
    }

    @Override
    public void set(IStateBitSet s) {
        lowerIndex = longSize;
        upperIndex = INDEX_OVERFLOW;
        boolean lbNeedChange = true;
        for (int i = 0; i < longSize; i++) {
            words[i] = s.getWord(i);
            if (lbNeedChange && words[i] != 0l && lowerIndex > i) {
                lowerIndex = i;
                lbNeedChange = false;
            }

            if (words[i] != 0l && upperIndex < i) {
                upperIndex = i;
            }
        }
        numBits = s.size();
    }

    @Override
    public void flip() {
//        boolean lbUnchanged = true;
        lowerIndex = longSize;
        upperIndex = INDEX_OVERFLOW;
        int len = longSize - 1;
        numBits = 0;
        for (int i = 0; i < len; ++i) {
            words[i] = ~words[i];
            numBits += Long.bitCount(words[i]);
            if (words[i] != 0) {
                lowerIndex = lowerIndex > i ? i : lowerIndex;
                upperIndex = upperIndex < i ? i : upperIndex;
            }
        }
        words[len] = ~words[len];
        words[len] &= lastMask;
        if (words[len] != 0) {
            lowerIndex = lowerIndex > len ? len : lowerIndex;
            upperIndex = upperIndex < len ? len : upperIndex;
        }
        numBits += Long.bitCount(words[len]);
    }

    @Override
    public boolean get(int bitIdx) {
        int wordIndex = wordIndex(bitIdx);
        return wordIndex < longSize && (this.words[wordIndex] & 1L << bitIdx) != 0L;
    }

    @Override
    public long getWord(int wordIdx) {
        return words[wordIdx];
    }

    @Override
    public void setWord(int wordIdx, long word) {
        long oldWord = words[wordIdx];
        words[wordIdx] = word;
        numBits = numBits - Long.bitCount(oldWord) + Long.bitCount(word);
    }

    @Override
    public void clear() {
        for (int i = 0; i < longSize; ++i) {
            words[i] = 0L;
        }
        lowerIndex = longSize;
        upperIndex = INDEX_OVERFLOW;
        numBits = 0;
    }

    @Override
    public void clear(int bitIdx) {
        int idx = wordIndex(bitIdx);
        // 原来是1 现在设置成0 changed = get(bitIdx) = true
        boolean changed = idx < longSize && (words[idx] & 1L << bitIdx) != 0L;
        if (changed) {
            words[idx] &= ~(1L << bitIdx);

            if (idx < lowerIndex) {
                lowerIndex = idx;
            }

            if (idx > upperIndex) {
                upperIndex = idx;
            }
            numBits--;
        }
    }

    @Override
    public int size() {
        return numBits;
    }

    @Override
    public int int64Size() {
        return longSize;
    }

    public int bitCount() {
        int sum = 0;
        for (int i = lowerIndex; i <= upperIndex; ++i)
            sum += Long.bitCount(words[i]);
        return sum;
    }

    @Override
    public void and(INaiveBitSet s) {
//        int i = INaiveBitSet.min(lowerIndex, s.firstSetIndex()),
//                ub = INaiveBitSet.max(upperIndex, s.lastSetIndex());
//        for (int i = lowerIndex; i <= upperIndex; ++i) {
//            words[i] &= s.getWord(i);
//        }
        for (int i = 0; i <= longSize; ++i) {
            words[i] &= s.getWord(i);
        }
    }

    @Override
    public void and(INaiveBitSet a, INaiveBitSet b) {
//        int i = INaiveBitSet.min(lowerIndex, a.firstSetIndex(), b.firstSetIndex()),
//                ub = INaiveBitSet.max(upperIndex, a.lastSetIndex(), b.lastSetIndex());
//        boolean lbChanged = false;
//        boolean upChanged = false;
//        for (int i = lowerIndex; i <= upperIndex; ++i) {
//            words[i] &= (a.getWord(i) & b.getWord(i));
//            if (!lbChanged&&words[i] != 0L) {
//                if ()
//            }
//        }

        numBits = 0;
        for (int i = 0; i < longSize; ++i) {
            words[i] &= (a.getWord(i) & b.getWord(i));
            numBits += Long.bitCount(words[i]);
        }
    }

    @Override
    public void and(INaiveBitSet a, INaiveBitSet b, INaiveBitSet c) {
//        int i = INaiveBitSet.min(lowerIndex, a.firstSetIndex(), b.firstSetIndex(), c.firstSetIndex()),
//                ub = INaiveBitSet.max(upperIndex, a.lastSetIndex(), b.lastSetIndex(), c.lastSetIndex());
        numBits = 0;
        for (int i = 0; i < longSize; ++i) {
            words[i] &= (a.getWord(i) & b.getWord(i) & c.getWord(i));
            numBits += Long.bitCount(words[i]);
        }
    }

    @Override
    public void or(INaiveBitSet s) {
        numBits = 0;
        for (int i = 0; i < longSize; ++i) {
            words[i] |= s.getWord(i);
            numBits += Long.bitCount(words[i]);
        }
    }

    @Override
    public void or(INaiveBitSet a, INaiveBitSet b) {
        numBits = 0;
        for (int i = 0; i < longSize; ++i) {
            words[i] |= a.getWord(i) | b.getWord(i);
            numBits += Long.bitCount(words[i]);
        }
    }

    @Override
    public void or(INaiveBitSet a, INaiveBitSet b, INaiveBitSet c) {
        numBits = 0;
        for (int i = 0; i < longSize; ++i) {
            words[i] |= a.getWord(i) | b.getWord(i) | c.getWord(i);
            numBits += Long.bitCount(words[i]);
        }
    }

    @Override
    public void andAfterMinus(INaiveBitSet a, INaiveBitSet b) {
        numBits = 0;
        for (int i = 0; i < longSize; ++i) {
            words[i] &= a.getWord(i) & ~b.getWord(i);
            numBits += Long.bitCount(words[i]);
        }
    }

    @Override
    public void orAfterMinus(INaiveBitSet a, INaiveBitSet b) {
        numBits = 0;
        for (int i = 0; i < longSize; ++i) {
            this.words[i] |= a.getWord(i) & ~b.getWord(i);
            numBits += Long.bitCount(words[i]);
        }
    }

    @Override
    public void setAfterMinus(INaiveBitSet a, INaiveBitSet b) {
        numBits = 0;
        for (int i = 0; i < longSize; ++i) {
            words[i] = a.getWord(i) & ~b.getWord(i);
            numBits += Long.bitCount(words[i]);
        }
    }

    @Override
    public void setAfterAnd(INaiveBitSet a, INaiveBitSet b) {
        numBits = 0;
        for (int i = 0; i < longSize; ++i) {
            words[i] = a.getWord(i) & b.getWord(i);
            numBits += Long.bitCount(words[i]);
        }
    }

    @Override
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

    @Override
    public int nextSetBit(int wordIndex, int bitIndex) {
        return Long.numberOfTrailingZeros(words[wordIndex] & -1L << bitIndex);
    }

    @Override
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

    @Override
    public int firstSetBit() {
        return (numBits == 0) ? INDEX_OVERFLOW : (64 * lowerIndex + Long.numberOfTrailingZeros(words[lowerIndex]));
    }

//    @Override
//    public int prevSetBit(int fromIndex) {
//        return 0;
//    }
//
//    @Override
//    public int prevClearBit(int fromIndex) {
//        return 0;
//    }

    @Override
    public boolean isEmpty() {
        return numBits == 0l;
    }

    @Override
    public int firstSetIndex() {
        return (numBits == 0l) ? INDEX_OVERFLOW : lowerIndex;
    }

    @Override
    public int lastSetIndex() {
        return (numBits == 0l) ? INDEX_OVERFLOW : upperIndex;
    }

    @Override
    public boolean isSingleton() {
        return numBits == 1;
    }

    @Override
    public int singleValue() {
        return (numBits == 1) ? firstSetBit() : INDEX_OVERFLOW;
    }

    @Override
    public int end() {
        return INDEX_OVERFLOW;
    }

    @Override
    public boolean overlap(INaiveBitSet s) {
        for (int i = 0; i <= longSize; ++i) {
            if((words[i] & s.getWord(i))!=0){
                return true;
            }
        }
        return false;
    }

    @Override
    public String toString() {
        StringBuilder ss = new StringBuilder();
        for (long w : words) {
            ss.append(Long.toBinaryString(w)).append(",");
        }
        return ss.substring(0, ss.length() - 1);
    }
}
