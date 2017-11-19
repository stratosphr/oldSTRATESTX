package lang.maths.exprs.set;

import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.Int;
import lang.maths.exprs.bool.ABoolExpr;

import java.util.Arrays;
import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:29
 */
public abstract class AInfiniteSetExpr extends ASetExpr {

    private final Int lowerBound;
    private final Int upperBound;
    private final LinkedHashSet<Int> excluded;

    AInfiniteSetExpr(Int lowerBound, Int upperBound, Int... excluded) {
        this.lowerBound = lowerBound;
        this.upperBound = upperBound;
        this.excluded = new LinkedHashSet<>(Arrays.asList(excluded));
    }

    public final boolean hasLowerBound() {
        return lowerBound != null;
    }

    public final boolean hasUpperBound() {
        return upperBound != null;
    }

    @Override
    public boolean isEmpty() {
        return false;
    }

    public Int getLowerBound() {
        return lowerBound;
    }

    public Int getUpperBound() {
        return upperBound;
    }

    public LinkedHashSet<Int> getExcluded() {
        return excluded;
    }

    @Override
    public abstract ABoolExpr getDomainConstraint(AArithExpr expr);

}
