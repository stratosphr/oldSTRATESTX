package lang.maths.exprs.set.usuals;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.set.AInfiniteSetExpr;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 10:48
 */
abstract class AUsualSet extends AInfiniteSetExpr {

    AUsualSet(Int lowerBound, Int upperBound, Int... excluded) {
        super(lowerBound, upperBound, excluded);
    }

    @Override
    public LinkedHashSet<Const> getConsts() {
        return new LinkedHashSet<>();
    }

    @Override
    public LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return new LinkedHashSet<>();
    }

    @Override
    public LinkedHashSet<FunVar> getFunVars(DefsContext defsContext) {
        return new LinkedHashSet<>();
    }

    @Override
    public LinkedHashSet<Fun> getFuns() {
        return new LinkedHashSet<>();
    }

}
