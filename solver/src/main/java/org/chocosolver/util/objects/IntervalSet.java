package org.chocosolver.util.objects;

public interface IntervalSet {

    void add(int lb, int ub);

    void clear();

    boolean contains(int lb, int ub);
}
