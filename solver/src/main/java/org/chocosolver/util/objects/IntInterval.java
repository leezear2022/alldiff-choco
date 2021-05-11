package org.chocosolver.util.objects;

import org.chocosolver.util.objects.tree.Interval;

public class IntInterval implements Interval {
    private int l, r;

    public IntInterval(int lb, int ub) {
        l = lb;
        r = ub;
    }

    @Override
    public int start() {
        return l;
    }

    @Override
    public int end() {
        return r;
    }

    @Override
    public String toString() {
        return "(" + l + ", " + r + ')';
    }
}