package org.chocosolver.amtf;

import org.antlr.v4.runtime.misc.IntervalSet;

import gnu.trove.list.array.TIntArrayList;
import gnu.trove.set.TIntSet;
import gnu.trove.set.hash.TIntHashSet;
import org.chocosolver.util.objects.INaiveBitSet;
import org.chocosolver.util.objects.setDataStructures.iterable.IntIterableRangeSet;
import org.chocosolver.util.objects.tree.Interval;
import org.chocosolver.util.objects.tree.IntervalTree;
import org.chocosolver.util.objects.IntInterval;
import org.xcsp.common.domains.Values;

import java.util.BitSet;

//import org.objenesis.strategy.BaseInstantiatorStrategy;

public class amtf {
    public static void main(String[] args) {
////        BitSet org.chocosolver.amtf = new BitSet(10);
////        for (int i = 0; i < 10; i++) {
////            if ((i & 1) == 1) {
////                org.chocosolver.amtf.set(i);
////            }
////        }
////        for (int j = org.chocosolver.amtf.nextClearBit(0); j >= 0 && j < 10; j = org.chocosolver.amtf.nextClearBit(j + 1)) {
////            out.println(j);
////        }
//
//        IntTuple2 t1 = new IntTuple2(1, 1);
//        IntTuple2 t2 = new IntTuple2(2, 1);
//
////        if (t1 == t2) {
////            System.out.println("true");
////        } else {
////            System.out.println("false");
////        }
//
//        ArrayList<IntTuple2> ts = new ArrayList<>();
//
//
//        ts.add(t1);
//        ts.add(t2);
//        System.out.println(ts.size());
//        Iterator<IntTuple2> iter = ts.iterator();
//        while (iter.hasNext()) {
//            IntTuple2 t = iter.next();
//            out.println(t.a + ", " + t.b);
//            t.a++;
//            t.b++;
//
//        }
//
//        iter = ts.iterator();
//        while (iter.hasNext()) {
//            IntTuple2 t = iter.next();
//            out.println(t.a + ", " + t.b);
//        }
//
//        HashSet<IntTuple2> delta = new HashSet<>();
//        IntTuple2 t3 = new IntTuple2(2, 2);
//
//        delta.add(t1);
//        delta.add(t2);
//        delta.add(t3);
//
//        out.println(t1 == t3);
//        out.println(t1.equals(t3));
//        out.println(delta.contains(t3));
//
//        for (IntTuple2 t : delta) {
//            out.println(t);
//        }


//        System.out.println(INaiveBitSet.max(1, 2, 3, 4));
//        System.out.println(INaiveBitSet.max(4, 3, 2, 1));
//
//        INaiveBitSet bs2 = INaiveBitSet.makeBitSet(32, true);
////
//        System.out.println(bs2);

//        for (int i = bs2.firstSetBit(); i != bs2.end(); i = bs2.nextSetBit(i + 1)) {
//            System.out.println(i);
//        }

//
//        INaiveBitSet bs = INaiveBitSet.makeBitSet(150, true);
////        bs.set(70);
////        bs.set(72);
////        bs.set(73);
////        bs.set(74);
////        bs.set(71);
//        System.out.println(bs);
//        bs.clear(0);
//        bs.clear(124);
////        System.out.println(bs.size());
////        int fsi = bs.firstSetIndex();
////        System.out.println(fsi);
////        System.out.println(bs.firstSetBit());
////        System.out.println(bs.singleValue());
//        System.out.println(nextSetBit(bs.getWord(0), 64));
//        System.out.println(nextSetBit(-1, 64));
//        System.out.println(Long.toBinaryString(-1L & -1L << 63));
//        System.out.println(Long.toBinaryString(-1L & -1L << 64));
////        for (int i = bs.firstSetBit(); i != -1; i = bs.nextSetBit(i + 1)) {
////            System.out.println(i);
////        }
//        System.out.println("--------------------");
//        int newNode = 0, iBase = 0;
//        for (int iWord = bs.firstSetIndex(); iWord <= bs.lastSetIndex(); ++iWord) {
//            long values = bs.getWord(iWord);
//            iBase = iWord * 64;
//
//            for (int i = nextSetBit(values, 0); i != 64; values &= ~(1L << i), i = nextSetBit(values, 0)) {
//                newNode = iBase + i;
//                System.out.println(newNode);
//            }
//        }

//        INaiveBitSet a = INaiveBitSet.makeBitSet(5, false);
//        a.set(1);
//        a.set(2);
//        a.set(4);
//        INaiveBitSet b = INaiveBitSet.makeBitSet(5, false);
//        b.set(2);
//        b.set(3);
//        b.set(4);
//
//        INaiveBitSet c = INaiveBitSet.makeBitSet(5, false);
//
//        b.setAfterMinus(a, b);
//        System.out.println(b);


//        TIntArrayList t = new TIntArrayList(2);
//        long haha = 0xffffffffffffffffL;
//        BitSet aa = new BitSet(64);
//        aa.set(0, 63);
//        System.out.println(aa);
//        System.out.println(aa.previousClearBit(62));
//
//        TIntSet ss = new TIntHashSet();
//        ss.add(1);
//        ss.add(1);
//        ss.add(2);
//
//        System.out.println(ss);

//        IntervalSet s = new IntervalSet();
//        s.add(1, 2);
//        s.add(2, 3);
//        s.add(3, 4);
//        IntIterableRangeSet is = new IntIterableRangeSet(new int[]{1, 2, 4, 4, 6, 7, 9, 13, 15, 15});
//        System.out.println(is);
//        is.add(3);
//        System.out.println(is);
//        for (var a : is) {
//            System.out.println(a);
//        }

//        IntervalTree<IntInterval> it = new IntervalTree();
//
////        t.insert()
//        IntInterval t = new IntInterval(1, 2);
//
////        System.out.println(t);
//
//        it.insert(t);
//        it.insert(new IntInterval(3, 4));
//
//        for (var tt : it) {
//            System.out.println(tt);
//        }
//        System.out.println("--------");
//        it.insert(new IntInterval(2, 3));
//
//        for (var tt : it) {
//            System.out.println(tt);
//        }
//        System.out.println("--------");
//        var con = it.contains(new IntInterval(1, 4));
//        System.out.println(con);
//        System.out.println("--------");
//        IntervalSet is = new IntervalSet();
//        is.add(0,1);
////        is.add(2,3);
//        is.add(4,5);
//        is.add(5,7);
//
////        is.add(0,1);
//        System.out.println(is);
//        System.out.println(is.contains(6));
//        System.out.println(is.or());

//        BitSet

    }

    private static int nextSetBit(long word, int pos) {
        return Long.numberOfTrailingZeros(word & -1L << pos);
    }
}
