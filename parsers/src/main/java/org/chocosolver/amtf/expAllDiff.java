package org.chocosolver.amtf;

import org.chocosolver.amtf.parser.XCSPParser;
//import org.chocosolver.parser.xcsp.XCSPParser;
import org.chocosolver.solver.Model;
import org.chocosolver.solver.Solver;
import org.chocosolver.solver.search.strategy.Search;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.Measurer;

import java.io.*;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.*;

import static java.lang.System.out;

public class expAllDiff {


    public static void main(String[] args) {

//        String inputFolder = "G:\\X3Benchmarks\\alldiff\\";
//        String outputFolder = "G:\\X3Benchmarks\\alldiff-result\\";
//        String[] series = new String[]{
//                "Langford-m1-k2",
//                "Langford-m1-k3",
//                "Langford-m1-k4",
////                "Queens-m1-s1",
//                "ColouredQueens-m1-s1",
////                "SchurrLemma-mod-s1",
////                "LatinSquare-m1-gp",
////                "LatinSquare-m1-gs",
////                "LatinSquare-xcsp2-bqwh15-106",
////                "LatinSquare-xcsp2-bqwh18-141",
//        };
        String[] HeuNames = {"ABS", "IBS", "WDEG", "CHS", "DEFAULT"};
        assert args.length == 2;
        Bench_File File_Benchmark = new Bench_File(args[0]);
        int heuIdx = Integer.parseInt(args[1]);
        String HeuName = HeuNames[heuIdx];
//        File_Benchmark.Print();
        String inputFolder = File_Benchmark.path_in;
        String outputFolder = File_Benchmark.path_out;
        ArrayList<String> series = File_Benchmark.all;
        Collections.sort(series);
        System.out.println(series);

        //获取时间
        DateTimeFormatter dateTimeFormatter = DateTimeFormatter.ofPattern("YYYY-MM-dd:HH:mm:ss");
        String dateTime = LocalDateTime.now().format(dateTimeFormatter);

        XCSPParser parser = new XCSPParser();
        String[] algorithms = new String[]{
                "AC_REGIN",
                "ACFair",
                "ACZhang18",
                "ACZhang18M",
                "ACZhang20",
                "ACNaive",
                "BC",
        };

        int runNum = 1;
        long node = 0;
        float time, matchingTime, filterTime, numDelValuesP1, numDelValuesP2, numProp, numNone, numSkip, numP1, numP2, numP1AndP2;
        float IN_SEC = 1000 * 1000 * 1000f;

        for (String s : series) {
            try {
                File csv = new File(outputFolder + s + "_" + HeuName + "_" + dateTime + ".csv");
                BufferedWriter bw = new BufferedWriter(new FileWriter(csv, false));
                bw.write("instance");
                for (int i = 0; i < algorithms.length; i++) {
                    bw.write(",algorithm,node,time,matchingTime,filterTime,numDelValuesP1,numDelValuesP2,numProp,numNone,numSkip,numP1,numP2,numP1AndP2");
//                    bw.write(",node,time");
                }
                bw.newLine();
                // 读取实例集s下的所有实例文件名
                File[] instances = new File(inputFolder + s).listFiles();
                List<File> fileList = Arrays.asList(instances);
                fileList.sort((o1, o2) -> {
                    if (o1.isDirectory() && o2.isFile())
                        return -1;
                    if (o1.isFile() && o2.isDirectory())
                        return 1;
                    return o1.getName().compareTo(o2.getName());
                });

                for (File ins : fileList) {
                    out.println(ins.getName());
                    bw.write(ins.getName());
                    for (String algorithm : algorithms) {
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
                        dateTime = LocalDateTime.now().format(dateTimeFormatter);
                        out.println(algorithm + "_" + dateTime + "======>");
                        for (int i = 0; i < runNum; i++) {
                            Measurer.initial();
                            Model model = new Model();
                            try {
                                parser.model(model, ins.getPath(), algorithm);
                            } catch (Exception e) {
                                e.printStackTrace();
                            }

                            if (Measurer.numAllDiff > 0) {
                                break;
                            }

                            IntVar[] decVars = (IntVar[]) model.getHook("decisions");

                            if (decVars == null) {
                                decVars = parser.mvars.values().toArray(new IntVar[parser.mvars.size()]);
                            }
                            Arrays.sort(decVars, Comparator.comparingInt(IntVar::getId));
                            Solver solver = model.getSolver();
                            solver.limitTime("900s");
//                            solver.setSearch(activityBasedSearch(decVars));
                            switch (heuIdx) {
                                case 0:
                                    solver.setSearch(Search.VarH.ABS.make(solver, decVars, Search.ValH.MIN, true));
                                case 1:
                                    solver.setSearch(Search.VarH.IBS.make(solver, decVars, Search.ValH.MIN, true));
                                case 2:
                                    solver.setSearch(Search.VarH.DOMWDEG.make(solver, decVars, Search.ValH.MIN, true));
                                case 3:
                                    solver.setSearch(Search.VarH.CHS.make(solver, decVars, Search.ValH.MIN, true));
                                case 4:
                                    solver.setSearch(Search.VarH.DEFAULT.make(solver, decVars, Search.ValH.MIN, true));
                            }
//                            solver.setSearch(Search.defaultSearch(model));
                            solver.solve();
                            // if (solver.solve()) {
                            // out.printf("solution: ");
                            // for (IntVar v : decVars) {
                            //     out.printf("%d ", v.getValue());
                            // }
                            // out.println();
                            // }
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

                        }
                        bw.write("," + algorithm + "," + node + "," + time + "," + matchingTime + "," + filterTime + "," + numDelValuesP1 + "," + numDelValuesP2 + "," + numProp
                                + "," + numNone + "," + numSkip + "," + numP1 + "," + numP2 + "," + numP1AndP2);
//                        bw.write("," + node + "," + time);
                        bw.flush();
                    }
                    bw.newLine();
                }
                bw.close();
            } catch (FileNotFoundException e) {
                e.printStackTrace();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
    }

}
