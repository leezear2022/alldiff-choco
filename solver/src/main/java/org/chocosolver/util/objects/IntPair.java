package org.chocosolver.util.objects;

import java.util.Objects;

public class IntPair {
    public int a;
    public int b;

    public IntPair(int x, int y) {
        this.a = x;
        this.b = y;
    }

    public boolean overlap(IntPair t) {
        return (t.a >= a && t.a <= b) || (t.b >= a && t.b <= b);
    }

    public boolean overlap(int x, int y) {
        return (x >= a && x <= b) || (y >= a && y <= b);
    }

    // this interval is in t
    public boolean in(IntPair t) {
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

    public static boolean EQ(IntPair t1, IntPair t2) {
        return t1.a == t2.a && t1.b == t2.b;
    }

    public boolean covered(int x, int y) {
        return x <= a && b <= y;
    }

    public static boolean Overlap(IntPair t1, IntPair t2) {
        return (t1.a >= t2.a && t1.a <= t2.b) || (t1.b >= t2.a && t1.b <= t2.b);
    }

    @Override
    public String toString() {
        return "(" + a + ", " + b + ")";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        IntPair t = (IntPair) o;
        return a == t.a && b == t.b;
    }

    @Override
    public int hashCode() {
        return Objects.hash(a, b);
    }
}
