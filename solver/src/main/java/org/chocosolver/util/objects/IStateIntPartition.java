package org.chocosolver.util.objects;

import org.chocosolver.memory.IEnvironment;
import org.chocosolver.memory.IStateInt;

public class IStateIntPartition extends IStatePartition {
    IStateInt sccMask;
    private static final int WORD_MASK = 0xffffffff;
    private static final int ADDRESS_BITS_PER_WORD = 5;
    private static final int BITS_PER_WORD = 1 << ADDRESS_BITS_PER_WORD;
    private static final int BIT_INDEX_MASK = BITS_PER_WORD - 1;

    IStateIntPartition(int arity, IEnvironment e) {
        super(arity);
        sccMask = e.makeInt();
        //1000,0100
        // scc start with 1bit
        maskSet(0);
    }

    @Override
    void maskSet(int e) {
        sccMask.set(sccMask.get() | (1 << e));
    }

    @Override
    void maskClear(int e) {
        sccMask.set(sccMask.get() & (~(1 << e)));
    }

    @Override
    void maskClear() {
        sccMask.set(0);
    }

    @Override
    boolean maskGet(int e) {
        return (sccMask.get() & (1L << e)) != 0;
    }

    @Override
    int maskNextSetBit(int e) {
        if (e >= BITS_PER_WORD)
            return INDEX_OVERFLOW;
        int currentValue = sccMask.get() & (WORD_MASK << e);
        return (currentValue == 0) ? INDEX_OVERFLOW : Integer.numberOfTrailingZeros(currentValue);
    }

    @Override
    int maskNextClearBit(int e) {
        if (e >= BITS_PER_WORD)
            return INDEX_OVERFLOW;
        int currentValue = ~sccMask.get() & (WORD_MASK << e);
        return (currentValue == 0) ? INDEX_OVERFLOW : Integer.numberOfTrailingZeros(currentValue);
    }

    @Override
    int maskPrevSetBit(int e) {
        if (e < 0)
            return -1;
        int currentValue = sccMask.get() & (WORD_MASK >>> -(e + 1));
        return (currentValue == 0) ? INDEX_OVERFLOW : Integer.numberOfLeadingZeros(currentValue);
    }

    @Override
    int maskPrevClearBit(int e) {
        if (e < 0)
            return -1;
        int currentValue = ~sccMask.get() & (WORD_MASK >>> -(e + 1));
        return (currentValue == 0) ? INDEX_OVERFLOW : BIT_INDEX_MASK - Integer.numberOfLeadingZeros(currentValue);
    }

    @Override
    String maskStr() {
        return Integer.toBinaryString(sccMask.get());
    }
}
