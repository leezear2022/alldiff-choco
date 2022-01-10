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

import gnu.trove.iterator.TIntIntIterator;
import gnu.trove.map.hash.TIntIntHashMap;
import org.chocosolver.memory.IEnvironment;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.PropagatorPriority;
import org.chocosolver.solver.constraints.nary.alldifferent.algo.*;
import org.chocosolver.solver.exception.ContradictionException;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.ESat;
import org.chocosolver.util.objects.IStateBitSetPartition;
import org.chocosolver.util.objects.IStateLongPartition;
import org.chocosolver.util.objects.IStatePartition;

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
//        System.out.println("------");
//        System.out.println(this.getId() + ": ");
//
//        for (var v : variables) {
//            System.out.println(v);
//        }
//        System.out.println("------");
        int arity = variables.length;
        int numValues = hashValues(variables);

        if (arity <= 64 && numValues <= 64) {
            if (arity < numValues) {
                filter = new AlgoAllDiffAC_SimpleGentZhang1820DoubleSingle64(variables, this, getModel());
            } else {
                filter = new AlgoAllDiffAC_SimpleGentZhang20Single64(variables, this, getModel());
            }
        } else if (arity <= 64) {
            if (arity < numValues) {
                filter = new AlgoAllDiffAC_SimpleGentZhang1820Single64(variables, this, getModel());
            } else {
                filter = new AlgoAllDiffAC_SimpleGentZhang20Single64(variables, this, getModel());
            }
        } else {
            if (arity < numValues) {
                this.filter = new AlgoAllDiffAC_SimpleGentZhang1820(variables, this, getModel());
            } else {
                this.filter = new AlgoAllDiffAC_SimpleGentZhang20(variables, this, getModel());
            }
        }

//        }
//        Measurer.numAllDiff++;
    }

    public int hashValues(IntVar[] vars) {
        int arity = vars.length;
        int numValues;
        TIntIntHashMap val2Idx = new TIntIntHashMap();
        // 先将从0开始的变量论域进行编码，只编一个变量
        for (int i = 0; i < arity; ++i) {
            IntVar v = vars[i];
            if (v.getLB() == 0) {
                for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
                    if (!val2Idx.containsKey(j)) {
                        val2Idx.put(j, val2Idx.size());
                    }
                }
                break;
            }
        }

        // 全部从头编码
        for (int i = 0; i < arity; ++i) {
            IntVar v = vars[i];
            for (int j = v.getLB(), ub = v.getUB(); j <= ub; j = v.nextValue(j)) {
                if (!val2Idx.containsKey(j)) {
                    val2Idx.put(j, val2Idx.size());
                }
            }
        }

        numValues = val2Idx.size();

        return numValues;
    }

    //***********************************************************************************
    // PROPAGATION
    //***********************************************************************************

    @Override
    public void propagate(int evtmask) throws ContradictionException {
//        System.out.println("----------------" + this.getId() + " propagate----------------");
        filter.propagate();
    }

    @Override
    public ESat isEntailed() {
        return ESat.TRUE; // redundant propagator (used with PropAllDiffInst)
    }


}
