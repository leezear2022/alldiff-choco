package org.chocosolver.util.objects;


public class LargeBitSet extends NaiveBitSet {
    // 记录非0索引
    int indexIterator = -1;
    int bitIterator = -1;

    int[] dense;
    int[] sparse;


    // limit 为实际元素的个数 limit之前（不含limit）的为有效值，从limit开始是无效值
    int limit = 0;

    public static int INDEX_OVERFLOW = 0x3f3f3f;

    public LargeBitSet(int nbits) {
        super(nbits);
        dense = new int[longSize];
        sparse = new int[longSize];

        for (int i = 0; i < longSize; ++i) {
            dense[i] = i;
            sparse[i] = i;
        }
    }

    @Override
    public void clear() {
        for (int i = 0; i < limit; ++i) {
            this.words[dense[i]] = 0L;
        }
        limit = 0;
    }

    @Override
    public void flip() {
        int len = longSize - 1;
        for (int i = 0; i < len; ++i) {
            words[i] = ~words[i];
            if (words[i] == 0L) {
                remove(i);
            } else {
                add(i);
            }
        }

        // 最后一个
        if ((words[len] = (~words[len]) & lastMask) == 0L) {
            remove(len);
        } else {
            add(len);
        }
    }

    @Override
    public void set(int bitIndex) {
        int index = wordIndex(bitIndex);
        if (this.words[index] == 0L) {
            add(index);
        }
        this.words[index] |= 1L << bitIndex;
    }

    @Override
    public void clear(int bitIndex) {
        int index = wordIndex(bitIndex);
        this.words[index] &= ~(1L << bitIndex);
        if (this.words[index] == 0L) {
            remove(index);
        }
    }



//    @Override
//    public int nextSetBit(int fromIndex) {
//        if (fromIndex < 0) {
//            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
//        } else {
//            int u = wordIndex(fromIndex);
//            if (!notClearIndex.contain(u)) {
//                return -1;
//            } else {
//                long word;
//                notClearIndex.iterateValid(u);
//                for (word = this.words[notClearIndex.current()] & -1L << fromIndex; word == 0L; word = this.words[notClearIndex.current()]) {
//                    if (notClearIndex.hasNextValid()) {
//                        notClearIndex.next();
//                    } else {
//                        return -1;
//                    }
//                }
//
//                return u * 64 + Long.numberOfTrailingZeros(word);
//            }
//        }
//    }

//    private void add(int i ){
//
//    }
//
//    private remove(int i ){}
//
//    public void begin() {
//        bitIterator = -1;
//        notClearIndex.iterateValid();
//    }

//    public boolean hasNext() {
//
//    }

//    public int next() {
//        ++bitIterator;
//        long word;
//        int i = 0;
//        if (notClearIndex.hasNextValid()) {
//            i = notClearIndex.next();
//        } else {
//            return INDEX_OVERFLOW;
//        }
//        for (word = this.words[i] & -1L << bitIterator; word == 0L; word = this.words[i]) {
//            if (notClearIndex.hasNextValid()) {
//                i = notClearIndex.next();
//            } else {
//                return INDEX_OVERFLOW;
//            }
//        }
//
//        return i * 64 + Long.numberOfTrailingZeros(word);
//    }

    private void remove(int e) {
        if (contain(e)) {
            swap(dense[e], limit - 1);
            limit--;
        }
    }

    public void add(int e) {
        if (!contain(e)) {
            swap(dense[e], limit);
            limit++;
        }
    }

    private boolean contain(int e) {
        return sparse[e] < limit;
    }

    private void swap(int i, int j) {
        int tmp = dense[i];
        dense[i] = dense[j];
        dense[j] = tmp;
        sparse[dense[i]] = i;
        sparse[dense[j]] = j;
    }

//    @Override
//    public int nextSetBit(int fromIndex) {
//        if (fromIndex < 0) {
//            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
//        } else {
//            int u = wordIndex(fromIndex);
//            int v;
//            if (!notClearIndex.contain(u)) {
//                return -1;
//            } else {
//                long word;
//                notClearIndex.iterateValid(u);
//                v = notClearIndex.current();
//                for (word = this.words[v] & -1L << fromIndex; word == 0L; word = this.words[v]) {
//                    if (notClearIndex.hasNextValid()) {
//                        v = notClearIndex.next();
//                    } else {
//                        return -1;
//                    }
//                }
//
//                return v * 64 + Long.numberOfTrailingZeros(word);
//            }
//        }
//    }

    public void begin() {
        indexIterator = 0;
        bitIterator = -1;
    }

    public int next() {
        ++bitIterator;
        long word;
        for (word = this.words[dense[indexIterator]] & -1L << bitIterator; word == 0L; word = this.words[dense[indexIterator]]) {
            ++indexIterator;
            bitIterator = 0;
            if (indexIterator == limit) {
                return INDEX_OVERFLOW;
            }
        }
        bitIterator = Long.numberOfTrailingZeros(word);
        return dense[indexIterator] * 64 + bitIterator;
    }

    //    @Override
    public String toBinaryString() {
        final int MAX_INITIAL_CAPACITY = Integer.MAX_VALUE - 8;
        int numBits = longSize * BITS_PER_WORD;
        // Avoid overflow in the case of a humongous numBits
        int initialCapacity = (numBits <= (MAX_INITIAL_CAPACITY - 2) / 6) ?
                6 * numBits + 2 : MAX_INITIAL_CAPACITY;
        StringBuilder b = new StringBuilder(initialCapacity);
        b.append('{');

        begin();
        int i = next();
        while (i != INDEX_OVERFLOW) {
            System.out.println(i);
            b.append(i).append(" ");
//            while (true) {
////                if (++i < 0) break;
//                if ((i = next()) < 0) break;
//                int endOfRun = nextClearBit(i);
//                do {
//                    b.append(", ").append(i);
//                }
//                while (++i != endOfRun);
//            }
            i = next();
        }

        b.append('}');
        return b.toString();
    }
//    public void set(LargeBitSet s) {
//        for (int i = 0; i < longSize; ++i) {
//            this.words[i] = s.words[i];
//        }
//
//        notClearIndex.iterateValid();
//        while (notClearIndex.hasNextValid()) {
//            int index = notClearIndex.next();
//            this.words[index] = 0L;
//        }
//        notClearIndex.clear();
//    }

//    public void iterator() {
//        indexIterator = 0;
//        iterator = -1;
//    }

//    public boolean hasNext() {
//        if ((this.words[nonClearIndex[indexIterator]] & -1L << iterator + 1) == 0L && indexIterator + 1 == limit) {
//            return false;
//        } else {
//            return true;
//        }
//    }

//    public int next() {
////        ++iterator;
////        long word;
////        for (word = this.words[nonClearIndex[indexIterator]] & -1L << iterator; word == 0L; word = this.words[nonClearIndex[indexIterator]]) {
////            ++indexIterator;
////            if (indexIterator == limit) {
////                return -1;
////            }
////        }
////        iterator = nonClearIndex[indexIterator] * 64 + Long.numberOfTrailingZeros(word);
////        return iterator;
////        ++iterator;
////        notClearIndex.iterateValid();
////        while (notClearIndex.hasNextValid()) {
////            int index = notClearIndex.next();
////            this.words[index] = 0L;
////        }
////        notClearIndex.clear();
//
////        ++iterator;
////        long word;
////        for (word = this.words[nonClearIndex[indexIterator]] & -1L << iterator; word == 0L; word = this.words[nonClearIndex[indexIterator]]) {
////            ++indexIterator;
////            if (indexIterator == limit) {
////                return -1;
////            }
////        }
////        iterator = nonClearIndex[indexIterator] * 64 + Long.numberOfTrailingZeros(word);
//    }
}
