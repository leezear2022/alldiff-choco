package org.chocosolver.amtf;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;

public class Bench_File {
    public String path_in = null;
    public String path_out = null;
    public ArrayList<String> all;
//    private String file = "/root/Projects/sbt_choco/src/main/java/org.chocosolver.amtf/bench";
    private String file = "src/main/java/org/chocosolver/amtf/bench";
    private int index = 0;

    Bench_File(String number) {
        file += number;
        all = new ArrayList<>();
        Read_Txt();
        index = 0;
    }

    Boolean Read_Txt() {
        try {
            FileReader fr = new FileReader(file);
            BufferedReader bf = new BufferedReader(fr);
            String str;
            // 按行读取字符串
            while ((str = bf.readLine()) != null) {
                if (path_in == null)
                    path_in = str;
                else if (path_out == null)
                    path_out = str;
                else
                    all.add(str);
            }
            bf.close();
            fr.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
        return true;
    }

    void Print() {
        System.out.println("in: " + path_in);
        System.out.println("out: " + path_out);
        for (String v : all) {
            System.out.println("sss: " + v);
        }

    }

//    String Get_Next() {
//        if (index < all.size()) {
//            return path_in + all.get(index++);
//        } else
//            return null;
//    }
//
//    String Get_Out_file() {
//        return path_out;
//    }
}
