/*
 * This file is part of examples, http://choco-solver.org/
 *
 * Copyright (c) 2020, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package org.chocosolver.examples.exp;


import org.chocosolver.examples.nqueen.AbstractNQueen;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.search.strategy.Search;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.Measurer;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

import static java.lang.System.out;
import static org.chocosolver.solver.search.strategy.Search.minDomLBSearch;

/**
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 31/03/11
 */
public class NQueenGlobal extends AbstractNQueen {
    String algo;

    @Override
    public void buildModel() {
        model = new Model("NQueen");
        vars = new IntVar[n];
        IntVar[] diag1 = new IntVar[n];
        IntVar[] diag2 = new IntVar[n];

        for (int i = 0; i < n; i++) {
            vars[i] = model.intVar("Q_" + i, 1, n, false);
            diag1[i] = model.intOffsetView(vars[i], i);
            diag2[i] = model.intOffsetView(vars[i], -i);
        }

        model.allDifferent(vars, algo).post();
        model.allDifferent(diag1, algo).post();
        model.allDifferent(diag2, algo).post();
    }

    public NQueenGlobal(Model model, int n, String algo) {
        this.model = model;
        this.n = n;
        this.algo = algo;
    }

    @Override
    public void configureSearch() {
        model.getSolver().setSearch(minDomLBSearch(vars));
    }

    public static void main(String[] args) throws IOException {
        String name = "NQueen";
        // algorithms
        String[] algorithms = ExpConfig.algorithms;

        //get local time
        DateTimeFormatter dateTimeFormatter = DateTimeFormatter.ofPattern("YYYY-MM-dd_HH_mm_ss");
        String dateTime = LocalDateTime.now().format(dateTimeFormatter);

        //output files
        String outputFolder = "D:/exp/large";
        File csv = new File(outputFolder + "//" + name + "_" + dateTime + ".csv");
        BufferedWriter bw = new BufferedWriter(new FileWriter(csv, false));
        bw.write("instance");
        for (int i = 0; i < algorithms.length; i++) {
            bw.write(",algorithm,node,time,matchingTime,filterTime,numDelValuesP1,numDelValuesP2,numProp,numNone,numSkip,numP1,numP2,numP1AndP2,maxArity");
//                    bw.write(",node,time");
        }
        bw.newLine();
        //for statistics
        int runNum = 1;
        long node = 0;
        float time, matchingTime, filterTime, numDelValuesP1, numDelValuesP2, numProp, numNone, numSkip, numP1, numP2, numP1AndP2, maxArity;
        float IN_SEC = 1000 * 1000 * 1000f;

        for (int i = 5; i <= 500; i+=5) {
            // instance name
            String insName = name + "-" + i;
            bw.write(insName);
            out.println(insName + " [" + dateTime + "]======>");
            for (String algorithm : algorithms) {
                // initial
                time = 0f;
                matchingTime = 0f;
                filterTime = 0f;
                numDelValuesP1 = 0f;
                numDelValuesP2 = 0f;
                numProp = 0f;
                numNone = 0f;
                numSkip = 0f;
                numP1 = 0f;
                numP2 = 0f;
                numP1AndP2 = 0f;
                maxArity = 0f;
                dateTime = LocalDateTime.now().format(dateTimeFormatter);
                out.println("  " + algorithm + " [" + dateTime + "]======>");


                Measurer.initial();
                Measurer.maxAllDiffArity = 0l;
                Model model = new Model();
                NQueenGlobal instances = new NQueenGlobal(model, i, algorithm);
                instances.buildModel();

                Solver solver = model.getSolver();
                solver.limitTime("1200s");
                // heu
                solver.setSearch(Search.defaultSearch(model));
//                solver.setSearch(inputOrderLBSearch(instances.vars));

                solver.solve();

                node = solver.getNodeCount();
                time += solver.getTimeCount() / runNum;
                matchingTime += Measurer.matchingTime / IN_SEC / runNum;
                filterTime += Measurer.filterTime / IN_SEC / runNum;
                numDelValuesP1 += Measurer.numDelValuesP1 / runNum;
                numDelValuesP2 += Measurer.numDelValuesP2 / runNum;
                numProp += Measurer.numProp / runNum;
                numNone += Measurer.numNone / runNum;
                numSkip += Measurer.numSkip / runNum;
                numP1 += Measurer.numP1 / runNum;
                numP2 += Measurer.numP2 / runNum;
                numP1AndP2 += Measurer.numP1AndP2 / runNum;
                maxArity += Measurer.maxAllDiffArity / runNum;

                bw.write("," + algorithm + "," + node + "," + time + "," + matchingTime + "," + filterTime + "," + numDelValuesP1 + "," + numDelValuesP2 + "," + numProp
                        + "," + numNone + "," + numSkip + "," + numP1 + "," + numP2 + "," + numP1AndP2 + "," + maxArity);
//                        System.out.println("," + algorithm + "," + node + "," + time + "," + matchingTime + "," + filterTime + "," + numDelValuesP1 + "," + numDelValuesP2 + "," + numProp
//                                + "," + numNone + "," + numSkip + "," + numP1 + "," + numP2 + "," + numP1AndP2 + "," + numP1AndP2 + "," + maxArity);
//                        bw.write("," + node + "," + time);
                bw.flush();
            }
            bw.newLine();
        }
        bw.close();
    }
}
