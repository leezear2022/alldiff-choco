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
import org.chocosolver.examples.integer.Partition;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.constraints.Constraint;
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
import static java.util.Arrays.fill;

/**
 * CSPLib prob049:<br/>
 * "This problem consists in finding a partition of numbers 1..N into two sets A and B such that:
 * <ul>
 * <li>A and B have the same cardinality</li>
 * <li>sum of numbers in A = sum of numbers in B</li>
 * <li>sum of squares of numbers in A = sum of squares of numbers in B</li>
 * </ul>
 * <p/>
 * More constraints can thus be added, e.g also impose the equality on the sum of cubes.
 * There is no solution for N < 8."
 * <p/>
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 31/03/11
 */
public class PartitionExp {
    @Option(name = "-n", usage = "Partition size.", required = false)
    int N = 2 * 32;

    IntVar[] vars;
    IntVar[] Ovars;

    Constraint[] heavy = new Constraint[3];

    String algo;
    Model model;


    public PartitionExp(Model model, int n, String algo) {
        this.model = model;
        this.N = n;
        this.algo = algo;
    }

    public void buildModel() {
//        model = new Model("Partition " + N);
        int size = this.N / 2;
        IntVar[] x, y;
        x = model.intVarArray("x", size, 1, 2 * size, false);
        y = model.intVarArray("y", size, 1, 2 * size, false);

//        break symmetries
        for (int i = 0; i < size - 1; i++) {
            model.arithm(x[i], "<", x[i + 1]).post();
            model.arithm(y[i], "<", y[i + 1]).post();
        }
        model.arithm(x[0], "<", y[0]).post();
        model.arithm(x[0], "=", 1).post();

        IntVar[] xy = new IntVar[2 * size];
        for (int i = size - 1; i >= 0; i--) {
            xy[i] = x[i];
            xy[size + i] = y[i];
        }

        Ovars = new IntVar[2 * size];
        for (int i = 0; i < size; i++) {
            Ovars[i * 2] = x[i];
            Ovars[i * 2 + 1] = y[i];
        }

        int[] coeffs = new int[2 * size];
        for (int i = size - 1; i >= 0; i--) {
            coeffs[i] = 1;
            coeffs[size + i] = -1;
        }
        heavy[0] = model.scalar(xy, coeffs, "=", 0);
        heavy[0].post();

        IntVar[] sxy, sx, sy;
        sxy = new IntVar[2 * size];
        sx = new IntVar[size];
        sy = new IntVar[size];
        for (int i = size - 1; i >= 0; i--) {
            sx[i] = model.intVar("x^", 0, x[i].getUB() * x[i].getUB(), true);
            sxy[i] = sx[i];
            sy[i] = model.intVar("y^", 0, y[i].getUB() * y[i].getUB(), true);
            sxy[size + i] = sy[i];
            model.times(x[i], x[i], sx[i]).post();
            model.times(y[i], y[i], sy[i]).post();
            model.member(sx[i], 1, 4 * size * size).post();
            model.member(sy[i], 1, 4 * size * size).post();
        }
        heavy[1] = model.scalar(sxy, coeffs, "=", 0);
        heavy[1].post();

        coeffs = new int[size];
        fill(coeffs, 1);
        model.scalar(x, coeffs, "=", 2 * size * (2 * size + 1) / 4).post();
        model.scalar(y, coeffs, "=", 2 * size * (2 * size + 1) / 4).post();
        model.scalar(sx, coeffs, "=", 2 * size * (2 * size + 1) * (4 * size + 1) / 12).post();
        model.scalar(sy, coeffs, "=", 2 * size * (2 * size + 1) * (4 * size + 1) / 12).post();

        heavy[2] = model.allDifferent(xy, algo);
        heavy[2].post();

        vars = xy;
    }

    public void configureSearch() {
        model.getSolver().setSearch(Search.minDomLBSearch(Ovars));
    }

    public void solve() {
        model.getSolver().solve();

        StringBuilder st = new StringBuilder();
        if (ESat.TRUE == model.getSolver().isFeasible()) {
            int sum1 = 0, sum2 = 0;
            int i = 0;
            st.append(vars[i].getValue());
            sum1 += vars[i].getValue();
            sum2 += vars[i].getValue() * vars[i++].getValue();
            for (; i < N / 2; i++) {
                st.append(", ").append(vars[i].getValue());
                sum1 += vars[i].getValue();
                sum2 += vars[i].getValue() * vars[i].getValue();
            }
            st.append(": (").append(sum1).append(")~(").append(sum2).append(")\n");
            sum1 = sum2 = 0;
            st.append(vars[i].getValue());
            sum1 += vars[i].getValue();
            sum2 += vars[i].getValue() * vars[i++].getValue();
            for (; i < N; i++) {
                st.append(", ").append(vars[i].getValue());
                sum1 += vars[i].getValue();
                sum2 += vars[i].getValue() * vars[i].getValue();
            }
            st.append(": (").append(sum1).append(")~(").append(sum2).append(")\n");
        } else {
            st.append("INFEASIBLE");
        }
        System.out.println(st.toString());
    }

    public static void main(String[] args) throws IOException {
        String name = "Partition";
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

        for (int i = 64; i <= 512; i += 16) {
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
                PartitionExp instances = new PartitionExp(model, i, algorithm);
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
