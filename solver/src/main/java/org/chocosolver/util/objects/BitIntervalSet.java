package org.chocosolver.util.objects;

import java.util.BitSet;

public class BitIntervalSet implements IntervalSet {
    private BitSet lbs;
    private BitSet ubs;
    private int capacity;
    int ap = -1, bp = -1, an = -1, bn = -1, newStart = -1, newEnd = -1, lbsClearStart = -1, lbsClearEnd = -1, ubsClearStart = -1, ubsClearEnd = -1;

    public BitIntervalSet(int maxSize) {
        capacity = maxSize;
        lbs = new BitSet(maxSize);
        ubs = new BitSet(maxSize);
    }

    //    @Override
//    public void add(int lb, int ub) {
//        int lbsPrevLb = lbs.previousSetBit(lb);
//
//        int lbsPrevUb = lbs.previousSetBit(ub);
////        int ubsPrevLb = ubs.previousSetBit(lb);
////        int ubsPrevUb = ubs.previousSetBit(ub);
//
//        if (lbsPrevLb == -1) {
//            // 若是第一个区间
//            if (lbsPrevUb == -1) {
//                // 若与现有区间没有交集，
//                ubs.set(ub);
//            } else {
//                // 若有交集：则取得现有区间[lbsPrevUb, ubs.nextSetBit(lbsPrevUb)]
//                // 合并新区间为[lb, max(ub, a)]
//                int a = Math.max(ub, ubs.nextSetBit(lbsPrevUb));
//                // 清除原来区间的标记
//                lbs.clear(lb + 1, lbsPrevUb + 1);
//                ubs.clear(lbsPrevUb, a);
//                //设置区间
//                ubs.set(a);
//            }
//            //设置区间
//            lbs.set(lb);
//        } else {
////            //若非第一个区间，则取得现有区间 [lbsPrevlb, a]
////            int a = ubs.nextSetBit(lbsPrevUb);
////            if (a < lb) {
////                // 现有前区间没有交集，直接添加
////                lbs.set(lb);
////                ubs.set(ub);
////            } else {
////                int b = Math.min(lb, lbsPrevUb);
////                int c = Math.max(ub, a);
////                lbs.clear(b, lbsPrevUb + 1);
////                ubs.clear(a, c);
////                lbs.set(b);
////                ubs.set(c);
////            }
//            int ubsNextPrevLb = ubs.nextSetBit(lbsPrevLb);
//            if (ubsNextPrevLb < lb) {
//                // [lb,ub]与前边的区间[lbsPrevLb,ubsNextPrevLb]无交集
//                if (lbsPrevUb < lb) {
//                    // 即lbsPrevUb = lbsPrevLb
//                    // 与后边的区间也没交集，即[lb,ub]之间完全没有区间的起点，即 完全没交集，直接添加,
//                    lbs.set(lb);
//                    ubs.set(ub);
//                } else {
//                    // [lb,ub]之间完有区间的起点，它的终点为ubs.nextSetBit(lbsPrevUb)
//                    // 新终点取newUb = max(ub,ubs.nextSetBit(lbsPrevUb));
//                    // 新区间为:[lb,newUb]
//                    int newUb = Math.max(ubs.nextSetBit(lbsPrevUb), ub);
//                    lbs.clear(lb + 1, lbsPrevUb + 1);
//                    ubs.clear(lb, newUb);
//                    lbs.set(lb);
//                    ubs.set(newUb);
//                }
//            } else {
//                // [lb,ub]与前边的区间[lbsPrevLb,ubsNextPrevLb]有交集
//                int newUb = Math.max(ubs.nextSetBit(lbsPrevUb), ub);
//                if (lbsPrevUb >= lb) {
//                    // 即lbsPrevUb != lbsPrevLb
//                    lbs.clear(lb, lbsPrevUb + 1);
//
//                }
//                ubs.clear(lb, newUb);
//                ubs.set(newUb);
//                lbs.set(lbsPrevLb);
////                int newLb = Math.min(lbs.previousSetBit(ubs.nextSetBit(lb)), lb);
////                int newUb = Math.max(ubs.nextSetBit(lbs.previousSetBit(ub)), ub);
////                ubs.set(newLb);
////                lbs.set(newUb);
//            }
//
////            int a = ubs.nextSetBit(lbsPrevLb);
////            if (a < lb) {
////                // 现有前区间没有交集
////                lbs.set(lb);
////                if (lbsPrevUb < lb) {
////                    //两区间没有交集，则直接添加
////
////                }
////                ubs.set(ub);
////            }
//        }
//
//    }

//    public void add(int start, int end) {
//        int newStart, newEnd, startPrev, endNext;
//        int endPrev = ubs.nextSetBit(start);
//        int startNext = lbs.previousSetBit(end);
//
//        if (endPrev == -1 || startNext == -1) {
//            lbs.set(start);
//            ubs.set(end);
//        } else {
//            startPrev = lbs.previousSetBit(endPrev);
//            endNext = ubs.nextSetBit(startNext);
//            if (endNext <= startPrev) {
//                lbs.set(start);
//                ubs.set(end);
//            } else {
//                newStart = Math.min(startPrev, start);
//                newEnd = Math.max(endNext, end);
////            if (newLb <= c + 1)
////                System.out.println(start + " " + end + " " + a + " " + b + " " + c + " " + d + " " + newLb + " " + newUb);
//                lbs.clear(newStart, startNext + 1);
////            if (b <= newUb + 1)
//                ubs.clear(endPrev, newEnd + 1);
//                lbs.set(newStart);
//                ubs.set(newEnd);
//            }
//        }
//    }

//    public void add(int start, int end) {
//        a = lbs.previousSetBit(start);
//        b = -1;
//        c = -1;
//        d = ubs.nextSetBit(end);
//
//        if (a != -1)
//            b = ubs.nextSetBit(a);
//
//        if (d != -1)
//            c = lbs.previousSetBit(d);
//
//        if (a==-1){}
//
//
//        lbs.clear(newStart, newEnd);
//        ubs.clear(newStart, newEnd);
//        lbs.set(newStart);
//        ubs.set(newEnd);
//    }

    public void add(int a, int b) {
        ap = lbs.previousSetBit(a);
        bn = ubs.nextSetBit(b);

        if (ap == -1) {
            newStart = a;
        } else {
            bp = ubs.nextSetBit(ap);
            newStart = (bp < a) ? a : ap;
//            if (bp < a) {
//                newStart = a;
//            } else {
//                newStart = ap;
//            }
        }

        if (bn == -1) {
            newEnd = b;
        } else {
            an = lbs.previousSetBit(bn);
            newEnd = b < an ? b : bn;
//            if (b < an) {
//                newEnd = b;
//            } else {
//                newEnd = bn;
//            }
        }

//        if((ap==-1&&bn==-1)||bp<a&&)

        lbs.clear(newStart, newEnd);
        ubs.clear(newStart, newEnd);
        lbs.set(newStart);
        ubs.set(newEnd);
    }

//    private boolean disjoint(int a, int b, int c, int d) {
//        return a > d || c > b;
//    }

    @Override
    public void clear() {
        lbs.clear();
        ubs.clear();
    }

    @Override
    public boolean contains(int lb, int ub) {
        ap = lbs.previousSetBit(lb);
//        int c = lbs.previousSetBit(ub);
        if (ap == -1) {
            return false;
        } else {
            bp = ubs.nextSetBit(ap);
            if (bp >= ub) {
                return true;
            } else {
                return false;
            }
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        int len = 0;
        sb.append("{");
        for (int i = lbs.nextSetBit(0); i != -1; i = lbs.nextSetBit(i + 1)) {
            int j = ubs.nextSetBit(i);
            sb.append(i).append("..").append(j).append(", ");
            len++;
        }
        if (len != 0) {
            sb.replace(sb.length() - 1, sb.length(), "}");
        }
        return sb.toString();
    }

//    public long size() {
//        return lbs.cardinality();
//    }
//    public boolean equalTo(IntIntervalSet s) {
//        for (int i = 0, ub = s.size(); i < ub; i++) {
//            var t = s.get(i);
//
//        }
//    }
}
