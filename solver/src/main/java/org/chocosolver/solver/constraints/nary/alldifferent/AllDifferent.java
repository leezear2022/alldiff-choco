/*
 * This file is part of choco-solver, http://choco-solver.org/
 *
 * Copyright (c) 2020, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package org.chocosolver.solver.constraints.nary.alldifferent;

import org.chocosolver.solver.constraints.Constraint;
import org.chocosolver.solver.constraints.ConstraintsName;
import org.chocosolver.solver.constraints.Propagator;
import org.chocosolver.solver.constraints.binary.PropNotEqualX_Y;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.util.objects.Measurer;

/**
 * Ensures that all variables from VARS take a different value.
 * The consistency level should be chosen among "AC", "BC", "FC" and "DEFAULT".
 */
public class AllDifferent extends Constraint {

    public static final String AC = "AC";
    public static final String AC20 = "AC20";
    public static final String AC_REGIN = "AC_REGIN";
    public static final String AC_ZHANG = "AC_ZHANG";
    public static final String BC = "BC";
    public static final String FC = "FC";
    public static final String Gent20 = "Gent20";
    public static final String Gent20BitIS = "Gent20BitIS";
    public static final String NEQS = "NEQS";
    public static final String DEFAULT = "DEFAULT";
    public static final String ACZhang20Choco = "ACZhang20Choco";
    public static final String ACZhang18M = "ACZhang18M";
    public static final String ACNaiveR = "ACNaiveR";
    public static final String ACNaiveNew = "ACNaiveNew";

    // 实验待测算法
    public static final String ACFair = "ACFair";
    public static final String ACChen = "ACChen";
    public static final String ACChen20 = "ACChen20";
    public static final String Gent = "Gent";
    public static final String WordRam = "WordRam";
    public static final String WordRamRegin = "WordRamRegin";
    public static final String WordRamGent = "WordRamGent";
    public static final String WordRamWordRam = "WordRamWordRam";
    public static final String WordRamZhang20 = "WordRamZhang20";
    public static final String WordRamZhang20BIS = "WordRamZhang20BIS";
    public static final String WordRamZhang20IS = "WordRamZhang20IS";
    public static final String WordRamZhang20BitBIS = "WordRamZhang20BitBIS";
    public static final String WordRamZhang20BitBIS2 = "WordRamZhang20BitBIS2";
    public static final String WordRamZhang20BitBIS4 = "WordRamZhang20BitBIS4";
    public static final String ACZhang18 = "ACZhang18";
    public static final String ACZhang20 = "ACZhang20";
    public static final String ACZhang20Bit = "ACZhang20Bit";
    public static final String ACNaive = "ACNaive";
    public static final String ACSimple = "ACSimple";
    public static final String ACSimpleGent = "ACSimpleGent";
    public static final String ACSimpleRegin = "ACSimpleRegin";
    public static final String ACSimpleGentZhang18 = "ACSimpleGentZhang18";
    public static final String ACSimpleGentZhang20 = "ACSimpleGentZhang20";
    public static final String ACSimpleGentZhang20Single64 = "ACSimpleGentZhang20Single64";

    public AllDifferent(IntVar[] vars, String type) {
        super(ConstraintsName.ALLDIFFERENT, createPropagators(vars, type));
        Measurer.maxAllDiffArity = Math.max(Measurer.maxAllDiffArity, vars.length);
        Measurer.numAllDiff++;
    }

    private static Propagator[] createPropagators(IntVar[] VARS, String consistency) {
        switch (consistency) {
            case NEQS: {
                int s = VARS.length;
                int k = 0;
                Propagator[] props = new Propagator[(s * s - s) / 2];
                for (int i = 0; i < s - 1; i++) {
                    for (int j = i + 1; j < s; j++) {
                        props[k++] = new PropNotEqualX_Y(VARS[i], VARS[j]);
                    }
                }
                return props;
            }
            case FC:
                return new Propagator[]{new PropAllDiffInst(VARS)};
            case BC:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffBC(VARS)};
            case AC_REGIN:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC(VARS, false)};
            case AC:
            case AC_ZHANG:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC(VARS, true)};
//            case Gent:
//                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Gent(VARS)};
            case ACFair:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Fair(VARS)};
            case ACChen:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Chen(VARS)};
            case ACChen20:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Chen20(VARS)};
            case ACZhang18:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Zhang18(VARS)};
            case ACZhang20:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Zhang20(VARS)};
//                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Gent20(VARS)};
            case ACZhang20Choco:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Zhang20Choco(VARS)};
            case AC20:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC20(VARS)};
//                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Gent20(VARS)};
//            case Gent20:
//                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Gent20(VARS)};
//            case ACZhang20Bit:
//                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Gent20Bit(VARS)};
//            case Gent20BitIS:
//                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Gent20BitIS(VARS)};
            case ACZhang18M:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Zhang18M(VARS)};
            case ACSimple:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Simple(VARS)};
            case ACSimpleRegin:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_SimpleRegin(VARS)};
            case ACSimpleGent:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_SimpleGent(VARS)};
            case ACSimpleGentZhang18:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_SimpleGentZhang18(VARS)};
            case ACSimpleGentZhang20:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_SimpleGentZhang20(VARS)};
            case ACSimpleGentZhang20Single64:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_SimpleGentZhang20Single64(VARS)};
            case ACNaive:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Naive(VARS)};
            case ACNaiveR:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_NaiveR(VARS)};
            case ACNaiveNew:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_NaiveBitSetNew(VARS)};
            case WordRam:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_WordRam(VARS)};
//                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_GentBit(VARS)};
            case WordRamRegin:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_WordRamRegin(VARS)};
            case WordRamGent:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_WordRamGent(VARS)};
//                case ACNaiveNew:
//                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_Naive(VARS)};
            case WordRamWordRam:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_WordRamWordRam(VARS)};
            case WordRamZhang20:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_WordRamZhang20(VARS)};
            case WordRamZhang20BIS:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_WordRamZhang20BIS(VARS)};
            case WordRamZhang20IS:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_WordRamZhang20IS(VARS)};
            case WordRamZhang20BitBIS:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_WordRamZhang20BitBIS(VARS)};
            case WordRamZhang20BitBIS2:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_WordRamZhang20BitBIS2(VARS)};
            case WordRamZhang20BitBIS4:
                return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffAC_WordRamZhang20BitBIS4(VARS)};
            case DEFAULT:
            default: {
                // adds a Probabilistic AC (only if at least some variables have an enumerated domain)
                boolean enumDom = false;
                for (int i = 0; i < VARS.length && !enumDom; i++) {
                    if (VARS[i].hasEnumeratedDomain()) {
                        enumDom = true;
                    }
                }
                if (enumDom) {
                    return new Propagator[]{new PropAllDiffInst(VARS), new PropAllDiffBC(VARS), new PropAllDiffAdaptative(VARS)};
                } else {
                    return createPropagators(VARS, "BC");
                }
            }
        }
    }
}
