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
import org.chocosolver.util.tools.StringUtils;
import org.kohsuke.args4j.Option;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.text.MessageFormat;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

import static java.lang.System.out;
import static org.chocosolver.solver.search.strategy.Search.inputOrderLBSearch;

/**
 * <a href="http://en.wikipedia.org/wiki/Latin_square">wikipedia</a>:<br/>
 * "A Latin square is an n x n array filled with n different Latin letters,
 * each occurring exactly once in each row and exactly once in each column"
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 15/06/11
 */
public class LatinSquareExp {

    @Option(name = "-n", usage = "Latin square size.", required = false)
    int m = 20;
    IntVar[] vars;

    String algo;
    Model model;

    public LatinSquareExp(Model model, int n, String algo) {
        this.model = model;
        this.m = n;
        this.algo = algo;
    }

    public void buildModel() {
//        model = new Model("Latin square");
        vars = new IntVar[m * m];
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < m; j++) {
                vars[i * m + j] = model.intVar("C" + i + "_" + j, 0, m - 1, false);
            }
        }
        // Constraints
        for (int i = 0; i < m; i++) {
            IntVar[] row = new IntVar[m];
            IntVar[] col = new IntVar[m];
            for (int x = 0; x < m; x++) {
                row[x] = vars[i * m + x];
                col[x] = vars[x * m + i];
            }
            model.allDifferent(col, algo).post();
            model.allDifferent(row, algo).post();
        }
    }

    public void configureSearch() {
        model.getSolver().setSearch(inputOrderLBSearch(vars));
    }

    public void solve() {
        model.getSolver().solve();

        StringBuilder st = new StringBuilder();
        String line = "+";
        for (int i = 0; i < m; i++) {
            line += "----+";
        }
        line += "\n";
        st.append(line);
        for (int i = 0; i < m; i++) {
            st.append("|");
            for (int j = 0; j < m; j++) {
                st.append(StringUtils.pad((char) (vars[i * m + j].getValue() + 97) + "", -3, " ")).append(" |");
            }
            st.append(MessageFormat.format("\n{0}", line));
        }
        st.append("\n\n\n");
        System.out.println(st.toString());
    }

    public static void main(String[] args) throws IOException {
        String name = "LantinSquare";
        // algorithms
        String[] algorithms = new String[]{
//                "AC_REGIN",
                "ACFair",
                "ACZhang18",
                "ACZhang18M",
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

        for (int i = 20; i <= 50; i++) {
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
