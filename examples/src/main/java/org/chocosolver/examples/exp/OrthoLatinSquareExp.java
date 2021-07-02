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
import org.chocosolver.solver.constraints.Constraint;
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
import java.util.ArrayList;
import java.util.List;

import static java.lang.System.arraycopy;
import static java.lang.System.out;


/**
 * Orthogonal latin square
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 15/06/11
 */
public class OrthoLatinSquareExp extends AbstractProblem {

    @Option(name = "-n", usage = "Ortho latin square size.", required = false)
    int m = 5;
    IntVar[] square1, square2, vars;
    Constraint[] ALLDIFFS;
    String algo;
    Model model;

    public OrthoLatinSquareExp(Model model, int n, String algo) {
        this.model = model;
        this.m = n;
        this.algo = algo;
    }

    @Override
    public void buildModel() {
        model = new Model();
        int mm = m * m;
        square1 = model.intVarArray("s1", mm, 1, m, true);
        square2 = model.intVarArray("s2", mm, 1, m, true);
        vars = model.intVarArray("vars", mm, 0, mm - 1, false);

        List<Constraint> ADS = new ArrayList<>();

        Constraint cc = model.allDifferent(vars, algo);
        cc.post();
        ADS.add(cc);

        int[] mod = new int[mm];
        int[] div = new int[mm];
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < m; j++) {
                mod[i * m + j] = j + 1;
                div[i * m + j] = i + 1;
            }
        }
        for (int i = 0; i < mm; i++) {
            model.element(square1[i], mod, vars[i], 0).post();
            model.element(square2[i], div, vars[i], 0).post();
        }

        // Rows
        for (int i = 0; i < m; i++) {
            IntVar[] ry = new IntVar[m];
            arraycopy(square1, i * m, ry, 0, m);
            cc = model.allDifferent(ry, algo);
            cc.post();
            ADS.add(cc);
            ry = new IntVar[m];
            arraycopy(square2, i * m, ry, 0, m);
            cc = model.allDifferent(ry, algo);
            cc.post();
            ADS.add(cc);
        }
        for (int j = 0; j < m; j++) {
            IntVar[] cy = new IntVar[m];
            for (int i = 0; i < m; i++) {
                cy[i] = square1[i * m + j];
            }
            cc = model.allDifferent(cy, algo);
            cc.post();
            ADS.add(cc);
            cy = new IntVar[m];
            for (int i = 0; i < m; i++) {
                cy[i] = square2[i * m + j];
            }
            cc = model.allDifferent(cy, algo);
            cc.post();
            ADS.add(cc);
        }
        ALLDIFFS = new Constraint[ADS.size()];
        ADS.toArray(ALLDIFFS);
        //TODO: ajouter LEX
        for (int i = 1; i < m; i++) {
            IntVar[] ry1 = new IntVar[m];
            IntVar[] ry2 = new IntVar[m];
            for (int j = 0; j < m; j++) {
                ry1[j] = square1[(i - 1) * m + j];
                ry2[j] = square2[i * m + j];
            }
            model.lexLess(ry1, ry2).post();
        }
    }

    @Override
    public void configureSearch() {
    }

    @Override
    public void solve() {
        model.getSolver().solve();

        System.out.println(String.format("Ortho latin square(%s)", m));
        StringBuilder st = new StringBuilder();
        st.append("\t");
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < m; j++) {
                st.append(String.format("%d ", square1[i * m + j].getValue()));
            }
            st.append("\n\t");
        }
        st.append("\n\t");
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < m; j++) {
                st.append(String.format("%d ", square2[i * m + j].getValue()));
            }
            st.append("\n\t");
        }
        System.out.println(st.toString());
    }


    public static void main(String[] args) throws IOException {
        String name = "OrthoLatinSquare";
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

        for (int i = 2; i <= 10; i++) {
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
                LatinSquareExp instances = new LatinSquareExp(model, i, algorithm);
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
