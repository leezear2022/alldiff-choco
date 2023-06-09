package org.chocosolver.amtf;

import org.chocosolver.amtf.parser.XCSPParser;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.search.strategy.Search;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.Measurer;

import java.util.Arrays;
import java.util.Comparator;

import static java.lang.System.out;


public class testAllDiff {

    public static void main(String[] args) {
        float IN_SEC = 1000 * 1000 * 1000f;

        String[] instances = new String[]{
//                "G:/X3Benchmarks/alldiff/GracefulGraph/GracefulGraph-m1-s1/GracefulGraph-K03-P05.xml",
//                "G:/X3Benchmarks/alldiff/Langford/Langford-m1-k2/Langford-2-08.xml",
//                "G:/X3Benchmarks/alldiff/Langford/Langford-m1-k4/Langford-4-07.xml",
//                "F:\\chenj\\data\\XCSP3\\Queens-m1-s1\\Queens-0050-m1.xml",
//                "G:\\X3Benchmarks\\alldiff\\Queens\\Queens-m1-s1\\Queens-0004-m1.xml",

//                "F:\\chenj\\data\\XCSP3\\AllDiff\\LatinSquare-xcsp2-bqwh15-106\\bqwh-15-106-02_X2.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff\\LatinSquare-xcsp2-bqwh15-106\\bqwh-15-106-03_X2.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff\\LatinSquare-xcsp2-bqwh18-141\\bqwh-18-141-01_X2.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff\\LatinSquare-xcsp2-bqwh18-141\\bqwh-18-141-02_X2.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff\\LatinSquare-xcsp2-bqwh18-141\\bqwh-18-141-03_X2.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff\\LatinSquare-m1-gp\\qwh-o30-h374-01.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff\\LatinSquare-m1-gp\\qwh-o30-h374-02.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff\\LatinSquare-m1-gp\\qwh-o30-h374-03.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff\\LatinSquare-m1-gp\\qwh-o30-h374-04.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff\\LatinSquare-m1-gs\\qwh-o010-h100.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff/ColouredQueens-m1-s1/ColouredQueens-03.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff/ColouredQueens-m1-s1/ColouredQueens-06.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff/ColouredQueens-m1-s1/ColouredQueens-07.xml",
//                "G:/X3Benchmarks/alldiff/ColouredQueens/ColouredQueens-m1-s1/ColouredQueens-09.xml",
//                "D:\\AllDiffBench\\DistinctVectors/DistinctVectors-30-010-02.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff\\SchurrLemma-mod-s1\\SchurrLemma-015-9-mod.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff\\SchurrLemma-mod-s1\\SchurrLemma-020-9-mod.xml",
//                "F:\\chenj\\data\\XCSP3\\AllDiff\\SchurrLemma-mod-s1\\SchurrLemma-030-9-mod.xml",
//                "C:\\bench\\X3\\Queens\\Queens-0004-m1.xml",
//                "C:\\bench\\X3\\SportsScheduling\\SportsScheduling-08.xml",
//                "C:\\bench\\X3\\SportsScheduling\\SportsScheduling-08.xml",
//                "/Users/lizhe/allDiff_Series/Queens/Queens-0008-m1.xml",
//                "/Users/leezear/allDiff_Series/Queens/Queens-0008-m1.xml",
//                "F:\\X3Benchmarks\\alldiff\\Queens-m1-s1\\Queens-0008-m1.xml"
//                "D:/AllDiffBench/ColouredQueens/ColouredQueens-07.xml",
//                "D:/AllDiffBench-1/Queens-m1-s1/Queens-0008-m1.xml",
//                "C:/exp/AllDiffBench-1/Queens-m1-s1/Queens-0030-m1.xml",
//                "C:\\exp\\AllDiffBench\\ColouredQueens\\ColouredQueens-07.xml",
//                "/Users/leezear/exp/AllDiffBench/ColouredQueens/ColouredQueens-08.xml",
//                "C:\\exp\\AllDiffBench\\SchurrLemma\\SchurrLemma-012-9-mod.xml",
//                "/Users/leezear/exp/AllDiffBench-1/GolombRuler/GolombRuler-11-a3.xml",
//                "/Users/leezear/exp/AllDiffBench-1/SchurrLemma/SchurrLemma-012-9-mod.xml",
//                "/home/lee/exp/AllDiffBench-1/SchurrLemma/SchurrLemma-012-9-mod.xml",
//                "/home/lee/exp/AllDiffBench-1/Ortholatin/",
//                "/home/lee/exp/AllDiffBench-1/NumberPartitioning/NumberPartitioning-008.xml",
//                "/home/lee/exp/AllDiffBench-1/NumberPartitioning/NumberPartitioning-032.xml",
//                "C:/exp/AllDiffBench-1/Kakuro/Kakuro-hard-070-sumdiff.xml",
//                "C:/exp/AllDiffBench-1/NumberPartitioning/NumberPartitioning-010.xml",
//                "C:/exp/AllDiffBench-1/CryptoPuzzle/CryptoPuzzle-black-green-orange.xml",
//                "/home/lee/exp/AllDiffBench-1/SportsScheduling/SportsScheduling-06.xml",
//                "/home/lee/exp/AllDiffBench/AllInterval/AllInterval-009.xml",

//                "/Users/leezear/exp/AllDiffBench-1/GolombRuler/GolombRuler-05-a3.xml",
//                "/Users/leezear/exp/AllDiffBench-1/GolombRuler/GolombRuler-07-a3.xml",
//                "/Users/leezear/exp/AllDiffBench-1/Queens-m1-s1/Queens-0004-m1.xml",
//                "/home/lee/exp/AllDiffBench-1/Queens-m1-s1/Queens-0012-m1.xml",
//                "/Users/leezear/exp/AllDiffBench/CostasArray/CostasArray-12.xml",
//                "C:\\exp\\AllDiffBench\\CostasArray\\CostasArray-10.xml",
//                "/Users/leezear/exp/AllDiffBench/GracefulGraph/GracefulGraph-K03-P04.xml",
//                "C:/exp/AllDiffBench/GracefulGraph/GracefulGraph-K02-P03.xml",
//                "C:/exp/AllDiffBench/GolombRuler/NumberPartitioning-032.xml",
//                "C:/exp/AllDiffBench/CryptoPuzzle/CryptoPuzzle-no-no-yes.xml",
//                "C:\\exp\\AllDiffBench\\GolombRuler\\GolombRuler-09-a3.xml",
//                "C:\\exp\\AllDiffBench\\Kakuro\\Kakuro-hard-038-sumdiff.xml",
//                "C:\\exp\\AllDiffBench-1\\Queens-m1-s1\\Queens-0012-m1.xml",
                "C:\\exp\\AllDiffBench\\AllInterval\\AllInterval-035.xml",
        };
        XCSPParser parser = new XCSPParser();
//        String[] algorithms = new String[]{
//                "AC_REGIN",
//                "ACFair",
////                "Gent",
////                "AC_ZHANG",
////                "AC20",
////                "Gent20",
////                "Gent20BitIS",
////                "ACZhang18",
////                "ACZhang18M",
////                "ACZhang18",
//                "ACZhang20",
////                "AC20",
////                "ACZhang20Choco",
////                "WordRam",
////                "WordRam2",
//                "ACZhang20Bit",
////                "ACNaive",
////                "ACNaiveNew",
////                "ACNaiveR",
////                "ACFair",
////                "AC_REGIN",
////                "ACNaive",
////                "ACFair",
////                "BC",
////                "Zhang18",
////                "AC_ZHANG",
//        };
        String[] algorithms = new String[]{
//                "AC",
//                "AC_ZHANG",
//                "ACFast",
//                "ACFast",
//                "ACFair",
//                "AC_REGIN",
//                "ACChen",
//                "ACZhang20Bit",
//                "ACChen20",
//                "Gent",
//                "Gent",
                "ACFair",
//                "ACFair",
//                "Gent20",
                "ACZhang18",
//                "ACZhang20",
//                "Gent20BitIS",
//                "ACZhang20Bit",
//                "WordRam",
//                "WordRamRegin",
                "WordRamGent",
                "WordRamWordRam",
                "WordRamWordRam2",
//                "WordRamWordRam",
//                "WordRamZhang20",
//                "WordRamZhang20BIS",
//                "ACZhang18",
//                "WordRamZhang20BitBIS",
//                "WordRamZhang20BitBIS2",
//                "WordRamZhang20BitBIS2",
//                "WordRamZhang20BitBIS4",
//                "WordRamZhang20BitBIS4",
//                "WordRamZhang20BitBIS4",
                "ACNaive",
//                "ACNaive",
//                "ACNaiveR",
//                "ACNaiveNew",
                "ACSimple",
//                "WordRamZhang20",
                "AC20",
//                "ACSimpleRegin",
//                "ACSimpleGent",
//                "ACSimpleGentZhang18",
//                "ACSimpleGentZhang20",
//                "ACSimpleGentZhang20Single64",
//                "AC",
        };
//        String[] algorithms = new String[]{
//                "ACNaive",
//                "ACNaive",
//                "ACNaiveNew",
//        };
        int runNum = 1;

        for (String ins : instances) {
            out.println(ins);
            for (String algo : algorithms) {
                out.println(algo + "====>");
                for (int i = 0; i < runNum; i++) {
                    Measurer.initial();
                    Measurer.maxAllDiffArity = 0l;
                    Model model = new Model();
                    try {
                        parser.model(model, ins, algo);
                    } catch (Exception e) {

                        e.printStackTrace();
                    }
                    IntVar[] decVars = (IntVar[]) model.getHook("decisions");
                    if (decVars == null) {
                        decVars = parser.mvars.values().toArray(new IntVar[0]);
                    }
                    Arrays.sort(decVars, Comparator.comparingInt(IntVar::getId));
                    Solver solver = model.getSolver();
//                    solver.setSearch(Search.defaultSearch(model));
//                    solver.setSearch(Search.VarH.DEFAULT.make(solver, decVars, Search.ValH.MIN, true));
                    solver.setSearch(Search.VarH.DOM.make(solver, decVars, Search.ValH.MIN, true));
//                    solver.setSearch(Search.VarH.INPUT.make(solver, decVars, Search.ValH.MIN, true));
//                    solver.setSearch(Search.VarH.RAND.make(solver, decVars, Search.ValH.MIN, true));
//                    solver.setSearch(Search.VarH.DOM.make(solver, decVars, Search.ValH.MIN, true));
//                    solver.setSearch(Search.activityBasedSearch(decVars));
//                    solver.setSearch(Search.minDomLBSearch(decVars));
//                    solver.setSearch(new ImpactBased(decVars, true));
//                    solver.setSearch(Search.VarH.ABS.make(solver, decVars, Search.ValH.MIN, true));
//                    solver.setSearch(Search.VarH.IBS.make(solver, decVars, Search.ValH.MIN, true));
//                    solver.setSearch(Search.VarH.DOMWDEG.make(solver, decVars, Search.ValH.MIN, true));
//                    solver.setSearch(Search.VarH.CHS.make (solver, decVars, Search.ValH.MIN, true));
//                  solver.setSearch(intVarSearch(new FirstFail(model), new IntDomainMin(), decVars));
//                  solver.setSearch(intVarSearch();

                    if (solver.solve()) {
                        if (i == runNum - 1) {
                            out.print("solution: ");
                            for (IntVar v : decVars) {
                                out.printf("%d ", v.getValue());
                            }
                            out.println();
                        }
                    }
                    if (i == runNum - 1) {
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
                        out.println("numFindSCC: " + Measurer.numFindSCC);
//                        solver.printStatistics();
                    }
                }
            }
        }
    }
}
