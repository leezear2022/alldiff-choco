package org.chocosolver.util.objects;

import org.chocosolver.memory.IStateBitSet;

public class Single32NaiveBitSet implements INaiveBitSet {
    protected int words;
    protected int lastMask;

    protected final static int ADDRESS_BITS_PER_WORD = 5;
    protected final static int BITS_PER_WORD = 1 << ADDRESS_BITS_PER_WORD;
    /* Used to shift left or right for a partial word mask */
    protected static final int WORD_MASK = 0xffffffff;
    protected static final int INDEX_OVERFLOW = -1;

    public Single32NaiveBitSet(int nbits, boolean initValue) {
        lastMask = WORD_MASK >>> (BITS_PER_WORD - nbits);
        if (initValue) {
            words = lastMask;
        }
    }


    @Override
    public void set() {
        words = lastMask;
    }

    @Override
    public void set(int bitIdx) {
        words |= 1 << bitIdx;
    }

    @Override
    public void set(INaiveBitSet s) {
        words = (int) s.getWord(0);
    }

    @Override
    public void set(IStateBitSet s) {
        words = (int) s.getWord(0);
    }

    @Override
    public void flip() {
        words = ~words;
        words &= lastMask;
    }

    @Override
    public boolean get(int bitIdx) {
        return (words & 1L << bitIdx) != 0;
    }

    @Override
    public long getWord(int wordIdx) {
        return words;
    }

    @Override
    public void setWord(int wordIdx, long word) {
        words = (int) word;
    }

    @Override
    public void clear() {
        words = 0;
    }

    @Override
    public void clear(int bitIdx) {
        words &= ~(1 << bitIdx);
    }

    @Override
    public int size() {
        return Integer.bitCount(words);
    }

    @Override
    public int int64Size() {
        return 1;
    }

    @Override
    public void and(INaiveBitSet s) {
        words &= (int) s.getWord(0);
    }

    @Override
    public void and(INaiveBitSet a, INaiveBitSet b) {
        words &= (int) (a.getWord(0) & b.getWord(0));
    }

    @Override
    public void and(INaiveBitSet a, INaiveBitSet b, INaiveBitSet c) {
        words &= (int) (a.getWord(0) & b.getWord(0) & c.getWord(0));
    }

    @Override
    public void or(INaiveBitSet s) {
        words |= (int) s.getWord(0);
    }

    @Override
    public void or(INaiveBitSet a, INaiveBitSet b) {
        words |= (int) a.getWord(0) | (int) b.getWord(0);
    }

    @Override
    public void or(INaiveBitSet a, INaiveBitSet b, INaiveBitSet c) {
        words |= (int) a.getWord(0) | (int) b.getWord(0) | (int) c.getWord(0);
    }

    @Override
    public void andAfterMinus(INaiveBitSet a, INaiveBitSet b) {
        words &= (int) a.getWord(0) & ~(int) b.getWord(0);
    }

    @Override
    public void orAfterMinus(INaiveBitSet a, INaiveBitSet b) {
        words |= (int) a.getWord(0) & ~(int) b.getWord(0);
    }

    @Override
    public void setAfterMinus(INaiveBitSet a, INaiveBitSet b) {
        words = (int) a.getWord(0) & ~(int) b.getWord(0);
    }

    @Override
    public void setAfterAnd(INaiveBitSet a, INaiveBitSet b) {
        words = (int) a.getWord(0) & (int) b.getWord(0);
    }

    @Override
    public int nextSetBit(int fromIndex) {
//        int a = Integer.numberOfTrailingZeros(words & -1 << fromIndex);
//        return a == BITS_PER_WORD ? INDEX_OVERFLOW : a;
        return Integer.numberOfTrailingZeros(words & -1 << fromIndex);
    }

    @Override
    public int nextSetBit(int wordIndex, int bitIndex) {
        return Integer.numberOfTrailingZeros(words & -1 << bitIndex);
    }

    @Override
    public int nextClearBit(int fromIndex) {
        int a = Integer.numberOfTrailingZeros(~words);
        return a == BITS_PER_WORD ? INDEX_OVERFLOW : a;
    }

    @Override
    public int firstSetBit() {
//        int a = Integer.numberOfTrailingZeros(words);
//        return a == BITS_PER_WORD ? INDEX_OVERFLOW : a;
        return Integer.numberOfTrailingZeros(words);
    }

    @Override
    public boolean isEmpty() {
        return words == 0;
    }

    @Override
    public int firstSetIndex() {
        return (words == 0) ? INDEX_OVERFLOW : 0;
    }

    @Override
    public int lastSetIndex() {
        return (words == 0) ? INDEX_OVERFLOW : 0;
    }

    @Override
    public boolean isSingleton() {
        return size() == 1;
    }

    @Override
    public int singleValue() {
        return (size() == 1) ? firstSetBit() : INDEX_OVERFLOW;
    }

    @Override
    public int end() {
        return BITS_PER_WORD;
    }

    @Override
    public boolean overlap(INaiveBitSet s) {
        return s.overlap(this);
    }

    @Override
    public String toString() {
//        return Integer.toBinaryString(words);
        if (size() == 0) {
            return "{}";
        }
        StringBuilder sb = new StringBuilder("{");
        for (int i = firstSetBit(); i < end(); i = nextSetBit(i + 1)) {
            sb.append(i).append(",");
        }
        sb.replace(sb.length() - 1, sb.length(), "}");
        return sb.toString();
    }
}
