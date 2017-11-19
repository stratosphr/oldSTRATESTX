package lang.maths.exprs.set;

import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.AValue;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.Equals;
import lang.maths.exprs.bool.Or;

import java.util.TreeSet;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:29
 */
public abstract class AFiniteSetExpr extends ASetExpr {

    public abstract TreeSet<AValue> getElements();

    public final int getCard() {
        return getElements().size();
    }

    @Override
    public final boolean isEmpty() {
        return getElements().isEmpty();
    }

    @Override
    public ABoolExpr getDomainConstraint(AArithExpr expr) {
        return new Or(getElements().stream().map(value -> new Equals(expr, value)).toArray(ABoolExpr[]::new));
    }

}
