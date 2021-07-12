package org.chocosolver.amtf;

import gnu.trove.list.array.TLongArrayList;
import org.chocosolver.util.objects.BitIntervalSet;
import org.chocosolver.util.objects.IntInterval;
import org.chocosolver.util.objects.IntIntervalSet;
import org.chocosolver.util.objects.IntTuple2;

import java.util.Arrays;
import java.util.Random;

public class IntervalExp {
    private static int INT_SIZE = 32;
    //    private TLongArrayStack DE;
    private static TLongArrayList cycles = new TLongArrayList(1000);
    private static IntTuple2 nodePair = new IntTuple2(-1, -1);

    public static void main(String[] args) {
        float IN_MSEC = 1000 * 1000f;
        int maxSize = 100;
//        int[] maxSizes={20,50,100,500,1000,5000,100000};
        assert args.length == 4;
        int insertBatch = Integer.parseInt(args[0]);
        int queryBatch = Integer.parseInt(args[1]);
        int stepFactor = Integer.parseInt(args[2]);
        boolean sorted = Integer.parseInt(args[3]) == 0 ? false : true;
        for (; maxSize < 1000000; maxSize *= 2) {
            Random rand = new Random();
            int total = 0;
            int correct = 0;
            int totalRound = maxSize / (insertBatch + queryBatch);
            int numInsert = totalRound * insertBatch;
            int numQuery = totalRound * queryBatch;
            IntInterval[] intervals = new IntInterval[numInsert];
            IntInterval[] queries = new IntInterval[numQuery];
            boolean[] ress = new boolean[numQuery];
            int maxStep = maxSize / numInsert * stepFactor;
            for (int i = 0; i < numInsert; ) {
                int step = rand.nextInt(maxStep);
                int start = rand.nextInt(maxSize);
                int end = start + step;
                if (end < maxSize && start != end) {
                    intervals[i] = new IntInterval(start, end);
//                    System.out.println(intervals[i]);
                    ++i;
                }
            }

            for (int i = 0; i < numQuery; ) {
                int step = rand.nextInt(maxStep);
                int start = rand.nextInt(maxSize);
                int end = start + step;
                if (end < maxSize && start != end) {
                    queries[i] = new IntInterval(start, end);
                    ++i;
                }
            }

//            System.out.println("------");
            if (sorted) {
                Arrays.sort(intervals);
            }
//
//            System.out.println(Arrays.toString(intervals));


            boolean res;

            cycles.clear();
            IntIntervalSet is = new IntIntervalSet();
            BitIntervalSet bbis = new BitIntervalSet(maxSize);

            double start;

            double[] time = new double[3];
            int i, j, up = Math.max(numInsert, numQuery);

            //****************************************************
            start = System.nanoTime();
            for (i = 0; i < totalRound; i++) {
                for (j = i * insertBatch; j < numInsert; j++) {
                    is.add(intervals[j].a, intervals[j].b);
                }

                for (j = i * queryBatch; j < numQuery; j++) {
                    ress[j] = is.contains(queries[j].a, queries[j].b);
                }
            }
            time[0] = (System.nanoTime() - start) / IN_MSEC;
            //****************************************************
            start = System.nanoTime();
            for (i = 0; i < totalRound; i++) {
                for (j = i * insertBatch; j < numInsert; j++) {
                    addCycles(getIntTuple2Long(intervals[j].a, intervals[j].b));
                }

                for (j = i * queryBatch; j < numQuery; j++) {
                    res = inCycles(getIntTuple2Long(queries[j].a, queries[j].b));
                    if (res == ress[j]) {
                        correct++;
                    }
                    total++;
                }
            }
            time[2] = (System.nanoTime() - start) / IN_MSEC;
            //****************************************************
            start = System.nanoTime();
            for (i = 0; i < totalRound; i++) {
                for (j = i * insertBatch; j < numInsert; j++) {
                    bbis.add(intervals[j].a, intervals[j].b);
                }

                for (j = i * queryBatch; j < numQuery; j++) {
                    res = bbis.contains(queries[j].a, queries[j].b);
                    if (res != ress[j]) {
//                        correct++;
                        System.out.println("xixi");
                    }
                }

            }
            time[1] = (System.nanoTime() - start) / IN_MSEC;
            //****************************************************

//            System.out.println("bbis: " + time);
            String sortStr = sorted ? "-S" : "";
            System.out.println(numInsert + "-" + numQuery + "-" + insertBatch + "-" + queryBatch + "-" + stepFactor + sortStr + "," + time[0] + "," + time[1] + "," + time[2] + "," + ((float) correct / total) + "," + (float) cycles.size() / is.numIntervals());
//            System.out.println(insertRound + "-" + queryRound + "-" + insertBatch + "-" + queryBatch + "-" + stepFactor + "-" + sorted + "," + time[0] + "," + time[1] + "," + time[2] + "," + ((float) correct / total) + "," + cycles.size() + "," + bbis.size() + "," + is.numIntervals());
        }
    }


    private static void addCycles(long e) {
        for (int i = 0; i < cycles.size(); i++) {
            long c = cycles.get(i);
            if (overlap(c, e)) {
                cycles.set(i, expand(c, e));
                return;
            }
        }
        cycles.add(e);
    }

    private static boolean inCycles(long f) {
////        IntTuple2 tt;
        getIntTuple2(nodePair, f);
////        System.out.println("inc:" + nodePair.a + "," + nodePair.b + "=" + varDFSNum[nodePair.a] + "," + valDFSNum[nodePair.b]);
//        // 小的存入a大的存入b
//        if (varDFSNum[nodePair.a] == Integer.MAX_VALUE || valDFSNum[nodePair.b] == Integer.MAX_VALUE) {
//            return false;
//        }
//
//        int a, b;
//        if (varDFSNum[nodePair.a] <= valDFSNum[nodePair.b]) {
//            a = varDFSNum[nodePair.a];
//            b = valDFSNum[nodePair.b];
//        } else {
//            a = valDFSNum[nodePair.b];
//            b = varDFSNum[nodePair.a];
//        }

        for (int i = 0, len = cycles.size(); i < len; ++i) {
            long e = cycles.get(i);
            if (cover(e, nodePair.a, nodePair.b)) {
                return true;
            }
        }

        return false;
    }

    public static long getIntTuple2Long(int x, int a) {
        long c = x;
        return c << INT_SIZE | a;
    }

    public static void getIntTuple2(IntTuple2 vvp, long vvpIdx) {
        vvp.a = (int) (vvpIdx >> INT_SIZE);
        vvp.b = (int) vvpIdx;
    }

    private static boolean cover(long e, int dfsa, int dfsb) {
        int a = (int) (e >> INT_SIZE);
        if (a == Integer.MAX_VALUE)
            return false;
        int b = (int) e;
        if (b == Integer.MAX_VALUE)
            return false;
//        int a = (int) (f >> INT_SIZE);
//        int b = (int) f;

        return (dfsa >= a && dfsa <= b) && (dfsb >= a && dfsb <= b);
    }

    private static boolean overlap(long e, long f) {
        int a = (int) (e >> INT_SIZE);
//        if (a == Integer.MAX_VALUE)
//            return false;
        int b = (int) e;
//        if (b == Integer.MAX_VALUE)
//            return false;
        int x = (int) (f >> INT_SIZE);
//        if (x == Integer.MAX_VALUE)
//            return false;
        int y = (int) f;
//        if (y == Integer.MAX_VALUE)
//            return false;
//        System.out.println("overlap: " + x + "," + y + "," + a + "," + b);
        return (x >= a && x <= b) || (y >= a && y <= b);
    }

    private static long expand(long e, long f) {
        int x = (int) (e >> INT_SIZE);
        int y = (int) e;
        int a = (int) (f >> INT_SIZE);
        int b = (int) f;
        return getIntTuple2Long(Math.min(x, a), Math.max(y, b));
    }


}
