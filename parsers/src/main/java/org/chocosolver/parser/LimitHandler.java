/*
 * This file is part of choco-parsers, http://choco-solver.org/
 *
 * Copyright (c) 2020, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package org.chocosolver.parser;

import org.chocosolver.util.tools.TimeUtils;
import org.kohsuke.args4j.CmdLineException;
import org.kohsuke.args4j.CmdLineParser;
import org.kohsuke.args4j.OptionDef;
import org.kohsuke.args4j.spi.OneArgumentOptionHandler;
import org.kohsuke.args4j.spi.Setter;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * <br/>
 *
 * @author Charles Prud'homme
 * @since 15/06/2020
 */
public class LimitHandler extends OneArgumentOptionHandler<ParserParameters.LimConf> {

    private static final Pattern Rp = Pattern.compile("(\\d+)runs");
    private static final Pattern Sp = Pattern.compile("(\\d+)sols");

    public LimitHandler(CmdLineParser parser, OptionDef option, Setter<? super ParserParameters.LimConf> setter) {
        super(parser, option, setter);
    }

    /**
     * Returns {@code "[String+]"}.
     *
     * @return return "[String+]";
     */
    @Override
    public String getDefaultMetaVariable() {
        return "[String+]";
    }


    @Override
    protected ParserParameters.LimConf parse(String argument) throws NumberFormatException, CmdLineException {
        if (argument.startsWith("[")) argument = argument.substring(1);
        if (argument.endsWith("]")) argument = argument.substring(0, argument.length() - 1);
        String[] pars = argument.split(",");
        long time = -1;
        int sols = -1;
        int runs = -1;
        for (String params : pars) {
            Matcher matcher = Rp.matcher(params);
            if (matcher.find() && matcher.groupCount() == 1) {
                runs = Integer.parseInt(matcher.group(1));
                continue;
            }
            matcher = Sp.matcher(params);
            if (matcher.find() && matcher.groupCount() == 1) {
                sols = Integer.parseInt(matcher.group(1));
                continue;
            }
            time = TimeUtils.convertInMilliseconds(params);
        }
        return new ParserParameters.LimConf(time, sols, runs);
    }
}
