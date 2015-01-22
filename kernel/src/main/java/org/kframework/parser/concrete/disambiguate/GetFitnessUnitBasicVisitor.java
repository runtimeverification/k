// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public abstract class GetFitnessUnitBasicVisitor extends BasicVisitor {
    public GetFitnessUnitBasicVisitor(Context context) {
        super(context);
    }

    protected int score = 0;

    public int getScore() {
        return score;
    }

    public void setScore(int score) {
        this.score = score;
    }

    public abstract GetFitnessUnitBasicVisitor getInstance();
}
