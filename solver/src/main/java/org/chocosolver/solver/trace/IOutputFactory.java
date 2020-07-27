/*
 * This file is part of choco-solver, http://choco-solver.org/
 *
 * Copyright (c) 2020, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package org.chocosolver.solver.trace;

import java.awt.image.BufferedImage;
import java.io.Closeable;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.List;
import javax.imageio.ImageIO;
import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.WindowConstants;
import org.chocosolver.solver.ISelf;
import org.chocosolver.solver.Solution;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.search.loop.monitors.IMonitorClose;
import org.chocosolver.solver.search.loop.monitors.IMonitorContradiction;
import org.chocosolver.solver.search.loop.monitors.IMonitorDownBranch;
import org.chocosolver.solver.search.loop.monitors.IMonitorInitialize;
import org.chocosolver.solver.search.loop.monitors.IMonitorSolution;
import org.chocosolver.solver.trace.frames.StatisticsPanel;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.Variable;
import org.chocosolver.util.tools.StringUtils;

/**
 * This aims at simplifying resolution trace output by providing
 * a unique entry point for most (not to say all) resolution message.
 * <br/>
 *
 * @author Charles Prud'homme
 * @version choco
 * @since 12/11/14
 */
public interface IOutputFactory extends ISelf<Solver> {
    /**
     * Set the current output stream (default is System.out)
     *
     * @param printStream a print stream
     */
    void setOut(PrintStream printStream);


    /**
     * @return the current output stream (default is System.out)
     */
    PrintStream getOut();

    /**
     * Set the current error stream (default is System.err)
     *
     * @param printStream a print stream
     */
    void setErr(PrintStream printStream);

    /**
     * @return the current error stream (default is System.err)
     */
    PrintStream getErr();


    /**
     * Print the version message.
     */
    default void printVersion() {
        getOut().println(ref().getModel().getSettings().getWelcomeMessage());
    }

    /**
     * Print (succint) features of the solver given in argument
     */
    default void printFeatures() {
        ref().getMeasures().setReadingTimeCount(System.nanoTime() - ref().getModel().getCreationTime());
        ref().getOut().printf("- Model[%s] features:\n", ref().getModel().getName());
        ref().getOut().printf("\tVariables : %d\n", ref().getModel().getNbVars());
        ref().getOut().printf("\tConstraints : %d\n", ref().getModel().getNbCstrs());
        ref().getOut().printf("\tBuilding time : %.3fs\n", ref().getMeasures().getReadingTimeCount());
        ref().getOut().printf("\tUser-defined search strategy : %s\n", ref().getModel().getSolver().isDefaultSearchUsed() ? "no" : "yes");
        ref().getOut().printf("\tComplementary search strategy : %s\n", ref().isSearchCompleted() ? "yes" : "no");
    }

    /**
     * Print (succint) features of the solver given in argument in a single line.
     */
    default void printShortFeatures() {
        ref().getMeasures().setReadingTimeCount(System.nanoTime() - ref().getModel().getCreationTime());
        String st = "Model[" + ref().getModelName() + "], "
            + String.format(
            "%d variables, %d constraints, building time: %.3fs, %s user-defined search strategy, %s complementary search strategy",
            ref().getModel().getNbVars(),
            ref().getModel().getNbCstrs(),
            ref().getMeasures().getReadingTimeCount(),
            ref().getModel().getSolver().isDefaultSearchUsed() ? "w/" : "w/o",
            ref().isSearchCompleted() ? "w/" : "w/o");
        getOut().println(st);
    }

    /**
     * Print the resolution statistics.
     * <p>
     * Recommended usage: to be called after the resolution step.
     */
    default void printStatistics() {
        printVersion();
        printFeatures();
        getOut().println(ref().getMeasures().toString());
    }

    /**
     * Output the resolution statistics in a single line.
     * <p>
     * Recommended usage: to be called after the resolution step.
     */
    default void printShortStatistics() {
        getOut().println(ref().getMeasures().toOneLineString());
    }

    /**
     * Output the resolution statistics in a comma-separated single line.
     * The header is:
     * <pre>
     *     solutionCount;buildingTime(sec);initTime(sec);initPropag(sec);totalTime(sec);objective;nodes;backtracks;fails;restarts;fineProp;coarseProp;
     * </pre>
     */
    default void printCSVStatistics() {
        getOut().println(ref().getMeasures().toCSV());
    }

    /**
     * Plug a search monitor which calls {@link #printVersion()}
     * and {@link #printStatistics()} before closing the search.
     * <p>
     * Recommended usage: to be called before the resolution step.
     */
    default void showStatistics() {
        ref().plugMonitor(new IMonitorInitialize() {

            @Override
            public void beforeInitialize() {
                printVersion();
                printFeatures();
            }
        });
        ref().plugMonitor(new IMonitorClose() {
            @Override
            public void afterClose() {
                getOut().println(ref().getMeasures().toString());
            }
        });
    }

    /**
     * Plug a search monitor which calls {@link #printShortStatistics()} before closing the search.
     * <p>
     * Recommended usage: to be called before the resolution step.
     */
    default void showShortStatistics() {
        ref().plugMonitor(new IMonitorClose() {
            @Override
            public void beforeClose() {
                printShortStatistics();
            }
        });
    }


    /**
     * Calls {@link #printShortStatistics()} before the program ends (normally or not)?
     * This adds a shutdown hook.
     * <p>
     * Recommended usage: to be called before the resolution step.
     */
    default void showShortStatisticsOnShutdown(){
        Runtime.getRuntime().addShutdownHook(new Thread(()-> ref().printShortStatistics()));
    }


    /**
     * Plug a search monitor which outputs {@code message} on each solution.
     * <p>
     * Recommended usage: to be called before the resolution step.
     *
     * @param message the message to print.
     */
    default void showSolutions(final IMessage message) {
        ref().plugMonitor((IMonitorSolution) () -> getOut().println(message.print()));
    }

    /**
     * Plug a search monitor which outputs a message on each solution.
     * <p>
     * Recommended usage: to be called before the resolution step.
     *
     * @see IOutputFactory.DefaultSolutionMessage
     */
    default void showSolutions() {
        showSolutions(new DefaultSolutionMessage(ref()));
    }

    /**
     * Plug a search monitor which outputs {@code message} on each decision.
     * <p>
     * Recommended usage: to be called before the resolution step.
     * @param message the message to print.
     */
    default void showDecisions(final IMessage message) {
        ref().plugMonitor(new IMonitorDownBranch() {
            @Override
            public void beforeDownBranch(boolean left) {
                getOut().printf("%s %s ", StringUtils.pad("", ref().getEnvironment().getWorldIndex(), "."),
                        ref().getDecisionPath().lastDecisionToString());
                getOut().printf(" // %s \n", message.print());
            }
        });
    }

    /**
     * Plug a search monitor which outputs a message on each decision.
     * <p>
     * Recommended usage: to be called before the resolution step.
     *
     * @see IOutputFactory.DefaultSolutionMessage
     */
    default void showDecisions() {
        showDecisions(new DefaultDecisionMessage(ref()));
    }

    /**
     * Plug a search monitor which outputs the contradictions thrown during the search.
     */
    default void showContradiction() {
        ref().plugMonitor((IMonitorContradiction) cex -> getOut().println(String.format("\t/!\\ %s", cex.toString())));
    }

    /**
     * Plug a search monitor which prints a one-line statistics every {@code f} ms.
     *
     * @param f      frequency, in millisecond
     */
    default void showStatisticsDuringResolution(long f) {
        if (f > 0) {
            ref().plugMonitor(new LogStatEveryXXms(ref(), f));
        }
    }


    /**
     * Create and show a simple dashboard that render resolution statistics every 100 milliseconds.
     */
    default void showDashboard(){
        this.showDashboard(100L);
    }

    /**
     * Create and show a simple dashboard that render resolution statistics every 'refresh' milliseconds.
     * Note that a low refresh rate will slow down the entire process.

     * @param refresh frequency rate, in milliseconds.
     */
    default void showDashboard(long refresh){
        //Make sure we have nice window decorations.
        JFrame.setDefaultLookAndFeelDecorated(true);

        //Create and set up the window.
        JFrame frame = new JFrame("Dashboard");
        frame.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);


        //Create and set up the content pane.
        JComponent newContentPane = new StatisticsPanel(ref(), refresh, frame);
        newContentPane.setOpaque(true); //content panes must be opaque
        frame.setContentPane(newContentPane);

        //Display the window.
        frame.pack();
//        frame.setLocationRelativeTo(null);
        frame.setVisible(true);
    }

    /**
     * Populate a DOT file (<i>gvFilename</i> with search tree to be vizualized with
     * <a href="https://graphviz.org">Graphviz</a>.
     * @param gvFilename dot filename
     * @return a {@link Closeable} object to be closed at the end of resolution
     */
    default Closeable outputSearchTreeToGraphviz(String gvFilename){
        return new GraphvizGenerator(gvFilename,this.ref());
    }

    /**
     * Populate a GEXF file (<i>gexfFilename</i> with search tree to be vizualized with
     * <a href="https://gephi.org">Gephi</a>.
     * @param gexfFilename dot filename
     * @return a {@link Closeable} object to be closed at the end of resolution
     */
    default Closeable outputSearchTreeToGephi(String gexfFilename){
        return new GephiGenerator(gexfFilename,this.ref());
    }

    /**
     * Plug <a href="https://github.com/cp-profiler/cp-profiler">cp-profiler</a> instance to this.
     * @param domain set to <i>true</i> to send variables' domain on each node, <i>false</i> otherwise.
     * @return a {@link Closeable} object to be closed at the end of resolution
     */
    default Closeable outputSearchTreeToCPProfiler(boolean domain){
        return new CPProfiler(this.ref(), domain);
    }

    /**
     * Populate a GEXF file (<i>gexfFilename</i> with constraint netwok to be vizualized with
     * <a href="https://gephi.org">Gephi</a>.
     * @param gexfFilename dot filename
     */
    default void constraintNetworkToGephi(String gexfFilename){
        GephiNetwork.write(gexfFilename, this.ref().getModel());
    }


    /**
     * Compute and print the distance matrix of integer solutions.
     * The Minkowski's p-distance is used
     * @param solutions list of solutions
     * @param p parameter p of p-distance (set to 2 for euclidean distance)
     */
    default void printDistanceMatrix(List<Solution> solutions, int p) {
        int n = solutions.size();
        IntVar[] vars = solutions.get(0).retrieveIntVars(true).toArray(new IntVar[0]);
        double[][] m = new double[n][n];
        for (int i = 0; i < n; i++) {
            Solution soli = solutions.get(i);
            for (int j = i + 1; j < n; j++) {
                Solution solj = solutions.get(j);
                double d = 0;
                for (int k = 0; k < vars.length; k++) {
                    double a = Math.abs(soli.getIntVal(vars[k]) - solj.getIntVal(vars[k]));
                    d += Math.pow(a, p);
                }
                m[i][j] = m[j][i] = Math.pow(d, 1. / p);
            }
            for (int j = 0; j < n; j++) {
                System.out.printf("%.3f ", m[i][j]);
            }
            System.out.print("\n");
        }
    }

    /**
     * Compute and print the distance matrix of integer solutions.
     * The Minkowski's p-distance is used
     * @param solutions list of solutions
     */
    default void printDifferenceMatrix(List<Solution> solutions) throws IOException {
        int n = solutions.size();
        IntVar[] vars = solutions.get(0).retrieveIntVars(true).toArray(new IntVar[0]);
        double[][] m = new double[n][n];
        BufferedImage biGray = new BufferedImage(n, n,BufferedImage.TYPE_INT_RGB);
        for (int i = 0; i < n; i++) {
            Solution soli = solutions.get(i);
            for (int j = i + 1; j < n; j++) {
                Solution solj = solutions.get(j);
                double d = 0;
                for (int k = 0; k < vars.length; k++) {
                    d += (soli.getIntVal(vars[k]) == solj.getIntVal(vars[k])) ? 0. : 1.;
                }
                m[i][j] = m[j][i] = d / vars.length;
            }
            for (int j = 0; j < n; j++) {
                int s = (int)(255 * (1-m[i][j]));
                biGray.setRGB(i, j,  (s << 16) | 255 << 8 | s);
                System.out.printf("%.3f ", m[i][j]);
            }
            System.out.print("\n");
        }
        File f = new File("MyFile.png");
        ImageIO.write(biGray, "PNG", f);
    }

    //////////////

    /**
     * The default solution message format
     */
    class DefaultSolutionMessage implements IMessage {

        /**
         * Solver to output
         */
        private Solver solver;

        /**
         * Create a solution message
         * @param solver solver to output
         */
        public DefaultSolutionMessage(Solver solver) {
            this.solver = solver;
        }

        @Override
        public String print() {
            return String.format("- Solution #%s found. %s \n\t%s.",
                    solver.getSolutionCount(),
                    solver.getMeasures().toOneLineString(),
                    print(solver.getSearch().getVariables())
            );
        }

        private String print(Variable[] vars) {
            StringBuilder s = new StringBuilder(32);
            for (Variable v : vars) {
                s.append(v).append(' ');
            }
            return s.toString();

        }
    }

    /**
     * The default decision message format
     */
    class DefaultDecisionMessage implements IMessage {

        /**
         * Solver to output
         */
        private Solver solver;

        /**
         * Create a decision message
         * @param solver solver to output
         */
        public DefaultDecisionMessage(Solver solver) {
            this.solver = solver;
        }

        @Override
        public String print() {
            int limit = 120;
            Variable[] vars = solver.getSearch().getVariables();
            StringBuilder s = new StringBuilder(32);
            for (int i = 0; i < vars.length && s.length() < limit; i++) {
                s.append(vars[i]).append(' ');
            }
            if (s.length() >= limit) {
                s.append("...");
            }
            return s.toString();
        }

    }
}
