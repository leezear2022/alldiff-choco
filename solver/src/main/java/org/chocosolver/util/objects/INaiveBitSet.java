package org.chocosolver.util.objects;

import org.chocosolver.memory.IStateBitSet;
import org.chocosolver.memory.structure.S64BitSet;

public interface INaiveBitSet {

    void set();

    void set(int bitIdx);

    void set(INaiveBitSet s);

    void set(IStateBitSet s);

    void flip();

    boolean get(int bitIdx);

    long getWord(int wordIdx);

    void setWord(int wordIdx, long word);

    void clear();

    void clear(int bitIdx);

    int size();

    int int64Size();

    void and(INaiveBitSet s);

    void and(INaiveBitSet a, INaiveBitSet b);

    void and(INaiveBitSet a, INaiveBitSet b, INaiveBitSet c);

    void or(INaiveBitSet s);

    void or(INaiveBitSet a, INaiveBitSet b);

    void or(INaiveBitSet a, INaiveBitSet b, INaiveBitSet c);

    void andAfterMinus(INaiveBitSet a, INaiveBitSet b);

    void orAfterMinus(INaiveBitSet a, INaiveBitSet b);

    void setAfterMinus(INaiveBitSet a, INaiveBitSet b);

    void setAfterAnd(INaiveBitSet a, INaiveBitSet b);

    int nextSetBit(int fromIndex);

    int nextClearBit(int fromIndex);

    int firstSetBit();

//    int lastSetBit();

//    int prevSetBit(int fromIndex);
//
//    int prevClearBit(int fromIndex);

    boolean isEmpty();

    int firstSetIndex();

    int lastSetIndex();

    boolean isSingleton();

    int singleValue();

    static final int INDEX_OVERFLOW = -1;

    static int min(int a, int b) {
        return (a <= b) ? a : b;
    }

    static int min(int a, int b, int c) {
//        return ((a <= b ? a : b) <= c) ? (a <= b ? a : b) : c;
        return ((a <= b ? a : b) <= c) ? a : c;
    }

    static int min(int a, int b, int c, int d) {
        return (((a <= b ? a : b) <= c) ? a : c) <= d ? a : d;
    }

    static int max(int a, int b) {
        return (a >= b) ? a : b;
    }

    static int max(int a, int b, int c) {
        return ((a >= b ? a : b) >= c) ? a : c;
    }

    static int max(int a, int b, int c, int d) {
        return (((a >= b ? a : b) >= c) ? a : c) >= d ? a : d;
    }

    static INaiveBitSet makeBitSet(int size, boolean initValue) {
        if (size < 32) {
            return new Single32NaiveBitSet(size, initValue);
        } else if (size < 64) {
            return new Single64NaiveBitSet(size, initValue);
        } else {
            return new NaiveBitSet(size, initValue);
        }
    }


}
