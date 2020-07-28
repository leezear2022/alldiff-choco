package org.chocosolver.solver.constraints.nary.alldifferent;

import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.constraints.nary.alldifferent.algo.AlgoAllDiffAC_Zhang18M;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.ESat;
import org.chocosolver.util.objects.Measurer;

//import org.chocosolver.solver.constraints.nary.alldifferent.algo.AlgoAllDiffACFast2;

public class PropAllDiffAC_Zhang18M extends Propagator<IntVar> {

    //***********************************************************************************
    // VARIABLES
    //***********************************************************************************

    protected AlgoAllDiffAC_Zhang18M filter;

    //***********************************************************************************
    // CONSTRUCTORS
    //***********************************************************************************

    /**
     * AllDifferent constraint for integer variables
     * enables to control the cardinality of the matching
     *
     * @param variables array of integer variables
     */
    public PropAllDiffAC_Zhang18M(IntVar[] variables) {
        super(variables, PropagatorPriority.QUADRATIC, false);
        this.filter = new AlgoAllDiffAC_Zhang18M(variables, this);
        Measurer.numAllDiff++;
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    @Override
    public void propagate(int evtmask) throws ContradictionException {
//        Measurer.numProp++;
//        System.out.println("----------------" + (Measurer.numProp) + ", " + this.getId() + " propagate----------------");
        filter.propagate();
    }

    @Override
    public ESat isEntailed() {
        return ESat.TRUE; // redundant propagator (used with PropAllDiffInst)
    }

}
