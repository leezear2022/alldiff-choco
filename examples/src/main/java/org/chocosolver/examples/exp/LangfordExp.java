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
import org.chocosolver.util.ESat;
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
 * CSPLib prob024:<br/>
 * "Consider two sets of the numbers from 1 to 4.
 * The problem is to arrange the eight numbers in the two sets into a single sequence in which
 * the two 1's appear one number apart,
 * the two 2's appear two numbers apart,
 * the two 3's appear three numbers apart,
 * and the two 4's appear four numbers apart.
 * <p/>
 * The problem generalizes to the L(k,n) problem,
 * which is to arrange k sets of numbers 1 to n,
 * so that each appearance of the number m is m numbers on from the last.
 * <br/>
 * For example, the L(3,9) problem is to arrange 3 sets of the numbers 1 to 9 so that
 * the first two 1's and the second two 1's appear one number apart,
 * the first two 2's and the second two 2's appear two numbers apart, etc."
 * <p/>
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 19/08/11
 */
public class LangfordExp {

    @Option(name = "-k", usage = "Number of sets.", required = false)
    private int k = 3;

    @Option(name = "-n", usage = "Upper bound.", required = false)
    private int n = 9;

    IntVar[] position;

    String algo;
    Model model;

    public LangfordExp(Model model, int k, int n, String algo) {
        this.model = model;
        this.k = k;
        this.n = n;
        this.algo = algo;
    }

    public void buildModel() {
        model = new Model();
        // position of the colors
        // position[i], position[i+k], position[i+2*k]... occurrence of the same color
        position = model.intVarArray("p", n * k, 0, k * n - 1, false);
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < this.k - 1; j++) {
                position[i + j * n].sub(i + 2).eq(position[i + (j + 1) * n]).post();
            }
        }
        position[0].lt(position[n * k - 1]).post();
        model.allDifferent(position, algo).post();
    }

    public void configureSearch() {
    }

    public void solve() {
        model.getSolver().solve();

        StringBuilder st = new StringBuilder(String.format("Langford's number (%s,%s)\n", k, n));
        if (model.getSolver().isFeasible() == ESat.TRUE) {
            int[] values = new int[k * n];
            for (int i = 0; i < k; i++) {
                for (int j = 0; j < n; j++) {
                    values[position[i * n + j].getValue()] = j + 1;
                }
            }
            st.append("\t");
            for (int i = 0; i < values.length; i++) {
                st.append(values[i]).append(" ");
            }
            st.append("\n");
        } else {
            st.append("\tINFEASIBLE");
        }
        System.out.println(st.toString());
    }

    public static void main(String[] args) throws IOException {
        String name = "Langford";
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

        // number of set
        int[] ks = {20, 100};
        // number in set
        int[] ns = {17, 25, 30, 37, 45};
        for (int i = 0; i < ks.length; i++) {
            int kk = ks[i];
            for (int j = 0; j <= ns.length; j++) {
                int nn = ns[j];
                // instance name
                String insName = name + "-" + kk + "-" + nn;
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
                    LangfordExp instances = new LangfordExp(model, kk, nn, algorithm);
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

        }
        bw.close();
    }

}
