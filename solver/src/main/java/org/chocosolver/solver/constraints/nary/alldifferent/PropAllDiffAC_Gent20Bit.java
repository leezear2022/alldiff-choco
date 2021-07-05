/*
 * This file is part of choco-solver, http://choco-solver.org/
 *
 * Copyright (c) 2020, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package org.chocosolver.solver.constraints.nary.alldifferent;

import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.constraints.nary.alldifferent.algo.AlgoAllDiffAC_Gent20;
import org.chocosolver.solver.constraints.nary.alldifferent.algo.AlgoAllDiffAC_Gent20Bit;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.ESat;

/**
 * Propagator for AllDifferent AC constraint for integer variables
 * <p/>
 * Uses Regin algorithm
 * Runs in O(m.n) worst case time for the initial propagation
 * but has a good average behavior in practice
 * <p/>
 * Runs incrementally for maintaining a matching
 * <p/>
 *
 * @author Jean-Guillaume Fages
 */
public class PropAllDiffAC_Gent20Bit extends Propagator<IntVar> {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************

        protected AlgoAllDiffAC_Gent20Bit filter;
//    protected AlgoAllDiffAC20 filter;
//    protected AlgoAllDiffAC_Gent20DEBit filter;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************

    /**
     * AllDifferent constraint for integer variables
     * enables to control the cardinality of the matching
     *
     * @param variables array of integer variables
     */
    public PropAllDiffAC_Gent20Bit(IntVar[] variables) {
        super(variables, PropagatorPriority.QUADRATIC, false);
//        filter = new AlgoAllDiffAC20(variables, this);
        filter = new AlgoAllDiffAC_Gent20Bit(variables, this, this.getModel());
//        filter = new AlgoAllDiffAC_Gent20DEBit(variables, this, this.getModel());
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