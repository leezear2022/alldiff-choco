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

import org.chocosolver.examples.AbstractProblem;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.search.strategy.Search;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.Measurer;
import org.kohsuke.args4j.Option;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

import static java.lang.System.out;

/**
 * CSPLib prob007:<br/>
 * "Given n in N, find a vector s = (s_1, ..., s_n), such that
 * <ul>
 * <li>s is a permutation of Z_n = {0,1,...,n-1};</li>
 * <li>the interval vector v = (|s_2-s_1|, |s_3-s_2|, ... |s_n-s_{n-1}|) is a permutation of Z_n-{0} = {1,2,...,n-1}.</li>
 * </ul>
 * <br/>
 * A vector v satisfying these conditions is called an all-interval series of size n;
 * the problem of finding such a series is the all-interval series problem of size n."
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 02/08/11
 */
public class AllIntervalSeriesExp {
    @Option(name = "-o", usage = "All interval series size.", required = false)
    private int m = 1000;

    @Option(name = "-v", usage = " use views instead of constraints.", required = false)
    private boolean use_views = false;

    IntVar[] vars;
    IntVar[] dist;

    String algo;
    Model model;

    public AllIntervalSeriesExp(Model model, int n, String algo) {
        this.model = model;
        this.m = n;
        this.algo = algo;
    }

    public void buildModel() {
//        model = new Model("AllIntervalSeries");
        vars = model.intVarArray("v", m, 0, m - 1, false);
        dist = new IntVar[m - 1];

        if (!use_views) {
            dist = model.intVarArray("dist", m - 1, 1, m - 1, false);
            for (int i = 0; i < m - 1; i++) {
                model.distance(vars[i + 1], vars[i], "=", dist[i]).post();
            }
        } else {
            for (int i = 0; i < m - 1; i++) {
                IntVar k = model.intVar(model.generateName(), -20000, 20000, true);
                model.sum(new IntVar[]{vars[i], k}, "=", vars[i + 1]).post();
                dist[i] = model.intAbsView(k);
                model.member(dist[i], 1, m - 1).post();
            }
        }

        model.allDifferent(vars, algo).post();
        model.allDifferent(dist, algo).post();

        // break symetries
        model.arithm(vars[1], ">", vars[0]).post();
        model.arithm(dist[0], ">", dist[m - 2]).post();
    }

    public void configureSearch() {
        model.getSolver().setSearch(Search.minDomLBSearch(vars));
    }

    public void solve() {
        model.getSolver().solve();
        System.out.println(String.format("All interval series(%s)", m));
        StringBuilder st = new StringBuilder();
        st.append("\t");
        for (int i = 0; i < m - 1; i++) {
            st.append(String.format("%d <%d> ", vars[i].getValue(), dist[i].getValue()));
            if (i % 10 == 9) {
                st.append("\n\t");
            }
        }
        st.append(String.format("%d", vars[m - 1].getValue()));
        System.out.println(st.toString());
    }

    public static void main(String[] args) throws IOException {
        String name = "AllInterval";
        // algorithms
        String[] algorithms = new String[]{
//                "AC_REGIN",
                "ACFair",
                "ACZhang18",
//                "ACZhang18M",
//                "ACZhang20",
                "AC20",
                "WordRam",
                "ACNaiveNew",
//                "BC",
        };

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

        for (int i = 4; i <= 30; i += 2) {
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
                AllIntervalSeriesExp instances = new AllIntervalSeriesExp(model, i, algorithm);
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
