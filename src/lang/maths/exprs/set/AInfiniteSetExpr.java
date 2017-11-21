package lang.maths.exprs.set;

import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.Int;
import lang.maths.exprs.bool.*;

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

    protected AInfiniteSetExpr(Int lowerBound, Int upperBound, Int... excluded) {
        this.lowerBound = lowerBound;
        this.upperBound = upperBound;
        this.excluded = new LinkedHashSet<>(Arrays.asList(excluded));
    }

    private boolean hasLowerBound() {
        return lowerBound != null;
    }

    private boolean hasUpperBound() {
        return upperBound != null;
    }

    @Override
    public boolean isEmpty() {
        return false;
    }

    @Override
    public ABoolExpr getDomainConstraint(AArithExpr expr) {
        ABoolExpr excludedConstraint = new Not(new Or(excluded.stream().map(anInt -> new Equals(expr, anInt)).toArray(ABoolExpr[]::new)));
        if (hasLowerBound() && hasUpperBound()) {
            return new And(new GEQ(expr, lowerBound), new LEQ(expr, upperBound), excludedConstraint);
        } else if (hasLowerBound()) {
            return new And(new GEQ(expr, lowerBound), excludedConstraint);
        } else if (hasUpperBound()) {
            return new And(new LEQ(expr, upperBound), excludedConstraint);
        } else {
            return excludedConstraint;
        }
    }

}
