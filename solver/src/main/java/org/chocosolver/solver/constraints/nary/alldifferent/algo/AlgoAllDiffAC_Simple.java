package org.chocosolver.solver.constraints.nary.alldifferent.algo;

import org.chocosolver.memory.IEnvironment;
import org.chocosolver.solver.ICause;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;

public abstract class AlgoAllDiffAC_Simple {

    public AlgoAllDiffAC_Simple(IntVar[] variables, ICause cause) {

    }

    public AlgoAllDiffAC_Simple(IntVar[] variables, ICause cause, IEnvironment e) {

    }

    public abstract boolean propagate() throws ContradictionException;
}
