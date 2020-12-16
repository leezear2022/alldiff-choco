package org.chocosolver.amtf;

import org.chocosolver.util.objects.IntTuple2;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

import static java.lang.System.out;

//import org.objenesis.strategy.BaseInstantiatorStrategy;

public class amtf {
    public static void main(String[] args) {
//        BitSet org.chocosolver.amtf = new BitSet(10);
//        for (int i = 0; i < 10; i++) {
//            if ((i & 1) == 1) {
//                org.chocosolver.amtf.set(i);
//            }
//        }
//        for (int j = org.chocosolver.amtf.nextClearBit(0); j >= 0 && j < 10; j = org.chocosolver.amtf.nextClearBit(j + 1)) {
//            out.println(j);
//        }

        IntTuple2 t1 = new IntTuple2(1, 1);
        IntTuple2 t2 = new IntTuple2(2, 1);

//        if (t1 == t2) {
//            System.out.println("true");
//        } else {
//            System.out.println("false");
//        }

        ArrayList<IntTuple2> ts = new ArrayList<>();


        ts.add(t1);
        ts.add(t2);
        System.out.println(ts.size());
        Iterator<IntTuple2> iter = ts.iterator();
        while (iter.hasNext()) {
            IntTuple2 t = iter.next();
            out.println(t.a + ", " + t.b);
            t.a++;
            t.b++;

        }

        iter = ts.iterator();
        while (iter.hasNext()) {
            IntTuple2 t = iter.next();
            out.println(t.a + ", " + t.b);
        }

        HashSet<IntTuple2> delta = new HashSet<>();
        IntTuple2 t3 = new IntTuple2(2,2);

        delta.add(t1);
        delta.add(t2);
        delta.add(t3);

        out.println(t1==t3);
        out.println(t1.equals(t3));
        out.println(delta.contains(t3));

        for (IntTuple2 t:delta){
            out.println(t);
        }

    }
}
