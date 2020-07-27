/*
 * This file is part of choco-solver, http://choco-solver.org/
 *
 * Copyright (c) 2020, IMT Atlantique. All rights reserved.
 *
 * Licensed under the BSD 4-clause license.
 *
 * See LICENSE file in the project root for full license information.
 */
package org.chocosolver.memory;

/**
 * A condition for building fake history based on the world index of the environment.
 * If the world index differs from 0, then a fake history is build for the object.
 * <br/>
 *
 * @author Charles Prud'homme
 * @version choco
 * @since 24/09/2014
 */
public class Except_0 implements ICondition {

    private IEnvironment environment;

    @Override
    public void set(IEnvironment environment) {
        this.environment = environment;
    }

    @Override
    public boolean satisfied() {
        return this.environment.getWorldIndex() > 0;
    }
}
