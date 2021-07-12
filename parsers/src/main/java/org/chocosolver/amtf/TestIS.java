package org.chocosolver.amtf;

import org.chocosolver.util.objects.BitIntervalSet;
import org.chocosolver.util.objects.IntInterval;
import org.chocosolver.util.objects.IntIntervalSet;

import java.util.Random;

public class TestIS {
    public static void main(String[] args) {
        int maxSize = 100;
        Random rand = new Random();
        int insertRound = maxSize / 5;
        int queryRound = maxSize / 5;
        int jmax = insertRound / 5;
        IntInterval[] intervals = new IntInterval[insertRound];
        IntInterval[] queries = new IntInterval[queryRound];
        boolean[] ress = new boolean[queryRound];
        int maxStep = maxSize / insertRound * 5;
        for (int i = 0; i < insertRound; ) {
            int step = rand.nextInt(maxStep);
            int start = rand.nextInt(maxSize);
            int end = start + step;
            if (end < maxSize) {
                intervals[i] = new IntInterval(start, end);
//                System.out.println(intervals[i]);
                ++i;
            }
        }

        for (var s :
                intervals) {
            System.out.println(s);

        }

        IntIntervalSet is = new IntIntervalSet();
        BitIntervalSet bis = new BitIntervalSet(maxSize);

        for (int i = 0; i < insertRound; i++) {
            IntInterval t = intervals[i];
            is.add(t.a, t.b);
            bis.add(t.a, t.b);

            System.out.printf("add: %s\n", t);
            System.out.println(is);
            System.out.println(bis);
//            System.out.println(is.to);
        }

    }
}
