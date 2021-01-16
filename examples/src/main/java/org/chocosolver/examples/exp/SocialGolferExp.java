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
import org.chocosolver.solver.variables.BoolVar;
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
import static org.chocosolver.solver.search.strategy.Search.inputOrderUBSearch;
import static org.chocosolver.util.tools.ArrayUtils.flatten;

/**
 * CSPLib prob010:<br/>
 * "The coordinator of a local golf club has come to you with the following problem.
 * In her club, there are 32 social golfers, each of whom play golf once a week,
 * and always in groups of 4.
 * She would like you to come up with a schedule of play for these golfers,
 * to last as many weeks as possible, such that
 * no golfer plays in the same group as any other golfer on more than one occasion.
 * <p/>
 * The problem can easily be generalized to that of scheduling
 * m groups of
 * n golfers over
 * p weeks,
 * such that no golfer plays in the same group as any other golfer twice
 * (i.e. maximum socialisation is achieved)
 * "
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 19/08/11
 */
public class SocialGolferExp {

    // parameters g-w-s:
    // 3-5-2, 3-4-3, 4-7-2, 4-4-3, 5-7-3

    // SPORT SCHEDULING: s=2, w = g - 1

    @Option(name = "-g", aliases = "--group", usage = "Number of groups.", required = false)
    int g = 4;

    @Option(name = "-w", aliases = "--week", usage = "Number of weeks.", required = false)
    int w = 4;

    @Option(name = "-s", aliases = "--player", usage = "Number of players per group.", required = false)
    int s = 3;


    BoolVar[][][] P, M;

    String algo;
    Model model;

    SocialGolferExp(Model model, int g, int w, int s, String algo) {
        this.model = model;
        this.g = g;
        this.w = w;
        this.s = s;
        this.algo = algo;
    }

    public void buildModel() {
//        model = new Model();
        int p = g * s;  // number of players

        P = new BoolVar[p][g][w];
        // p plays in group g in week w
        for (int i = 0; i < p; i++) {
            P[i] = model.boolVarMatrix("p_" + i, g, w);
        }
        M = new BoolVar[p][p][w];
        // i meets j in week w (i<j)
        for (int i = 0; i < p; i++) {
            M[i] = model.boolVarMatrix("m_" + i, p, w);
        }

        // each player is part of exactly one group in each week
        for (int i = 0; i < p; i++) {
            for (int k = 0; k < w; k++) {
                IntVar[] player = new IntVar[g];
                for (int j = 0; j < g; j++) {
                    player[j] = P[i][j][k];
                }
                model.sum(player, "=", 1).post();
            }
        }

        // each group has exactly s players
        for (int j = 0; j < g; j++) {
            for (int k = 0; k < w; k++) {
                IntVar[] group = new IntVar[p];
                for (int i = 0; i < p; i++) {
                    group[i] = P[i][j][k];
                }
                model.sum(group, "=", s).post();
            }
        }

        // obvious filtering for M
        for (int i = 0; i < p; i++) {
            for (int l = 0; l < w; l++) {
                for (int j = i + 1; j < p; j++) {
                    model.arithm(M[i][j][l], "=", M[j][i][l]).post();
                }
                model.arithm(M[i][i][l], "=", 1).post();
            }
        }

        // link the M and P variables
        for (int i = 0; i < p - 1; i++) {
            for (int j = i + 1; j < p; j++) {
                for (int l = 0; l < w; l++) {
                    BoolVar[] group = new BoolVar[g];
                    for (int k = 0; k < g; k++) {
                        group[k] = model.and(P[i][k][l], P[j][k][l]).reify();
                        model.arithm(group[k], "<=", M[i][j][l]).post();
                    }
                    model.sum(group, "=", M[i][j][l]).post();
                }
            }
        }

        // each pair of players only meets once
        for (int i = 0; i < p - 1; i++) {
            for (int j = i + 1; j < p; j++) {
                model.sum(M[i][j], "=", model.boolVar("sum")).post();
            }
        }

        // break symmetries on first group
        for (int i = 1; i < p; i++) {
            model.lexLessEq(P[i][0], P[i - 1][0]).post();
        }
    }

    public void configureSearch() {
        BoolVar[] vars = flatten(P);
        model.getSolver().setSearch(inputOrderUBSearch(vars));
    }

    public void solve() {
        model.getSolver().solve();

        System.out.println(String.format("Social golfer(%d,%d,%d)", g, s, w));
        StringBuilder st = new StringBuilder();
        if (model.getSolver().isFeasible() == ESat.TRUE) {
            int p = g * s;
            for (int i = 0; i < w; i++) {
                st.append("\tWeek ").append(i + 1).append("\n");
                for (int j = 0; j < g; j++) {
                    st.append("\t\tGroup ").append(j + 1).append(": ");
                    for (int k = 0; k < p; k++) {
                        if (P[k][j][i].getValue() > 0) {
                            st.append(k).append(", ");
                        }
                    }
                    st.append("\n");
                }
                st.append("\n");
            }
        } else {
            st.append("\tINFEASIBLE");
        }
        System.out.println(st.toString());
    }

    public static void main(String[] args) throws IOException {
        String name = "SocialGolfer";
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
        int[] gs = {11, 14, 15};
        for (int i = 0; i < gs.length; i++) {
            int gg = gs[i];
            String insName = name + "-" + 9 + "-" + 4 + "-" + gg;
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
                SocialGolferExp instances = new SocialGolferExp(model, 9, gg, 4, algorithm);
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
}
