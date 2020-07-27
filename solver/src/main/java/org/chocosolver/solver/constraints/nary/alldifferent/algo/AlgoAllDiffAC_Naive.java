package org.chocosolver.solver.constraints.nary.alldifferent.algo;

import org.chocosolver.solver.ICause;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;

public abstract class AlgoAllDiffAC_Naive {
    public AlgoAllDiffAC_Naive(IntVar[] variables, ICause cause) {
    }

    public abstract boolean propagate() throws ContradictionException;
}
