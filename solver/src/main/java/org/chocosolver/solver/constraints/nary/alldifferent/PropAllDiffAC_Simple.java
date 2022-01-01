/*
 * This file is part of choco-solver, http://choco-solver.org/
 *
 * Copyright (c) 2019, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package org.chocosolver.solver.constraints.nary.alldifferent;

import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.constraints.nary.alldifferent.algo.AlgoAllDiffAC_Naive;
import org.chocosolver.solver.constraints.nary.alldifferent.algo.AlgoAllDiffAC_NaiveBitSet;
import org.chocosolver.solver.constraints.nary.alldifferent.algo.AlgoAllDiffAC_Simple;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.ESat;

/**
 * Propagator for AllDifferent AC constraint for integer variables
 * <p/>
 * Uses Zhang algorithm in the paper of IJCAI-18
 * "A Fast Algorithm for Generalized Arc Consistency of the Alldifferent Constraint"
 * <p>
 * We try to use the bit to speed up.
 * <p>
 * Runs in O(m.n) worst case time for the initial propagation
 * but has a good average behavior in practice
 * <p/>
 * Runs incrementally for maintaining a matching
 * <p/>
 *
 * @author Jia'nan Chen
 */

public class PropAllDiffAC_Simple extends Propagator<IntVar> {

    //***********************************************************************************0
    // VARIABLES
    //***********************************************************************************

    protected AlgoAllDiffAC_Simple filter;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************

    /**
     * AllDifferent constraint for integer variables
     * enables to control the cardinality of the matching
     *
     * @param variables array of integer variables
     */
    public PropAllDiffAC_Simple(IntVar[] variables) {
        super(variables, PropagatorPriority.QUADRATIC, false);

//        Measurer.maxAllDiffArity = Math.max(Measurer.maxAllDiffArity, vars.length);

//        if (vars.length <= 32) {
//            this.filter = new AlgoAllDiffAC_Naive32(variables, this);
//        } else if (vars.length <= 64) {
//            this.filter = new AlgoAllDiffAC_Naive64(variables, this);
//        } else {
        this.filter = new AlgoAllDiffAC_Simple(variables, this);
//        }
//        Measurer.numAllDiff++;
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    @Override
    public void propagate(int evtmask) throws ContradictionException {
//        System.out.println("----------------" + (Measurer.numProp) + ", " + this.getId() + " propagate----------------");
        filter.propagate();
    }

    @Override
    public ESat isEntailed() {
        return ESat.TRUE; // redundant propagator (used with PropAllDiffInst)
    }

}
