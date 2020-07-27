package org.chocosolver.amtf;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;

public class sortFile {
    public static void main(String[] args) {
        assert args.length == 1;
        Bench_File File_Benchmark = new Bench_File(args[0]);
//        File_Benchmark.Print();
        String inputFolder = File_Benchmark.path_in;
        String outputFolder = File_Benchmark.path_out;
        ArrayList<String> series = File_Benchmark.all;
        Collections.sort(series);
        System.out.println(series);

        for (String s : series) {
            try {
                File csv = new File(outputFolder + s + ".csv");
                File[] instances = new File(inputFolder + s).listFiles();
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
    }

}
