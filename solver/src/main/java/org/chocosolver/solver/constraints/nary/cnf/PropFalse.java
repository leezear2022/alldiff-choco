/*
 * This file is part of choco-solver, http://choco-solver.org/
 *
 * Copyright (c) 2020, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package org.chocosolver.solver.constraints.nary.cnf;

import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.learn.ExplanationForSignedClause;
import org.chocosolver.solver.learn.Implications;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.events.IntEventType;
import org.chocosolver.util.ESat;
import org.chocosolver.util.objects.ValueSortedMap;

/**
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 24 nov. 2010
 */
public class PropFalse extends Propagator<BoolVar> {

    public PropFalse(BoolVar zero) {
        super(new BoolVar[]{zero}, PropagatorPriority.UNARY, false);
    }

    @Override
    public void propagate(int evtmask) throws ContradictionException {
        fails();
    }

    @Override
    public int getPropagationConditions(int vIdx) {
        return IntEventType.all();
    }

    @Override
    public String toString() {
        return java.lang.Boolean.FALSE.toString();
    }

    @Override
    public ESat isEntailed() {
        return ESat.FALSE;
    }

    @Override
    public void explain(ExplanationForSignedClause explanation, ValueSortedMap<IntVar> front, Implications ig, int p) {
        // nothing to do
    }

}
