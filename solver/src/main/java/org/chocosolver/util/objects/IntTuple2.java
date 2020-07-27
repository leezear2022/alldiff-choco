package org.chocosolver.util.objects;

public class IntTuple2 {
    public int a;
    public int b;

    public IntTuple2(int x, int y) {
        this.a = x;
        this.b = y;
    }

    public boolean overlap(IntTuple2 t) {
        return (t.a >= a && t.a <= b) || (t.b >= a && t.b <= b);
    }

    public boolean overlap(int x, int y) {
        return (x >= a && x <= b) || (y >= a && y <= b);
    }

    // this interval is in t
    public boolean in(IntTuple2 t) {
        return a > t.a && b > t.b;
    }

    // this interval is in t
    public boolean in(int x, int y) {
        return a > x && b > y;
    }

    public boolean cover(int x, int y) {
        return a <= x && y <= b;
    }

    public boolean cover(int x) {
        return x >= a && x <= b;
    }

    public static boolean EQ(IntTuple2 t1, IntTuple2 t2) {
        return t1.a == t2.a && t1.b == t2.b;
    }

    public boolean covered(int x, int y) {
        return x <= a && b <= y;
    }

    public static boolean Overlap(IntTuple2 t1, IntTuple2 t2) {
        return (t1.a >= t2.a && t1.a <= t2.b) || (t1.b >= t2.a && t1.b <= t2.b);
    }

    @Override
    public String toString() {
        return "(" + a + ", " + b + ")";
    }
}
