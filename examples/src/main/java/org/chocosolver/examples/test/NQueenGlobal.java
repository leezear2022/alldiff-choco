/*
 * This file is part of examples, http://choco-solver.org/
 *
 * Copyright (c) 2020, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package org.chocosolver.examples.test;


import org.chocosolver.examples.exp.ExpConfig;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.search.strategy.Search;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.Measurer;

import java.io.IOException;

import static java.lang.System.out;

/**
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 31/03/11
 */
public class NQueenGlobal {
    protected final static float IN_SEC = 1000 * 1000 * 1000f;

    public Model buildModel(int n, String algo) {
        Model model = new Model("NQueen");

        IntVar[] vars = new IntVar[n];
        IntVar[] diag1 = new IntVar[n];
        IntVar[] diag2 = new IntVar[n];

        for (int i = 0; i < n; i++) {
            vars[i] = model.intVar("Q_" + i, 0, n-1, false);
            diag1[i] = model.intOffsetView(vars[i], i);
            diag2[i] = model.intOffsetView(vars[i], -i);
        }
        model.addHook("decisions", vars);
        model.allDifferent(vars, algo).post();
        model.allDifferent(diag1, algo).post();
        model.allDifferent(diag2, algo).post();

        return model;
    }

    public NQueenGlobal() {
    }
//
//    public void configureSearch() {
//        model.getSolver().setSearch(minDomLBSearch(vars));
//    }

    public static void main(String[] args) throws IOException {
//        String name = "NQueen";
        // algorithms
        String[] algorithms = ExpConfig.algorithms;
        int[] numQueens = {80};
//        int[] numQueens = {4, 8, 12, 16, 20};
        for (String algorithm : algorithms) {
            for (int n : numQueens) {
//                Model model = new Model(name);
                Measurer.initial();
                out.printf("NQueen-%d-%s====================>\n", n, algorithm);
                NQueenGlobal instances = new NQueenGlobal();
                Model model = instances.buildModel(n, algorithm);

                Solver solver = model.getSolver();
                solver.limitTime("1200s");
                IntVar[] decVars = (IntVar[]) model.getHook("decisions");
                // heu
//                solver.setSearch(Search.defaultSearch(model));
//                model.getSolver().setSearch(minDomLBSearch(decVars));
                solver.setSearch(Search.VarH.DOMWDEG.make(solver, decVars, Search.ValH.MIN, true));
//                solver.setSearch(Search.VarH.ABS.make(solver, decVars, Search.ValH.MIN, true));
                if (solver.solve()) {
                    out.print("solution: ");
                    for (IntVar v : decVars) {
                        out.printf("%d ", v.getValue());
                    }
                    out.println();
                }
                out.println("node: " + solver.getNodeCount());
                out.println("time: " + solver.getTimeCount() + "s");
                out.println("getDecisionPath: " + solver.getDecisionPath());
                out.println("getBackTrackCount: " + solver.getBackTrackCount());
                out.println("find matching time: " + Measurer.matchingTime / IN_SEC + "s");
                out.println("filter time: " + Measurer.filterTime / IN_SEC + "s");
//                        out.println("scc time: " + Measurer.checkSCCTime / IN_SEC + "s");
                out.println("numAllDiff: " + Measurer.numAllDiff);
                out.println("maxAllDiffArity: " + Measurer.maxAllDiffArity);
                out.println("numProp: " + Measurer.numProp);
                out.println("numNone: " + Measurer.numNone);
                out.println("numSkip: " + Measurer.numSkip);
                out.println("numP1: " + Measurer.numP1);
                out.println("numP2: " + Measurer.numP2);
                out.println("numP1AndP2: " + Measurer.numP1AndP2);
//                        solver.printStatistics();
            }
        }


    }
}
