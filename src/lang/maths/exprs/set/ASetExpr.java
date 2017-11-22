package lang.maths.exprs.set;

import lang.AObject;
import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.AValue;
import lang.maths.exprs.arith.Int;
import lang.maths.exprs.bool.ABoolExpr;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:29
 */
public abstract class ASetExpr extends AObject {

    public abstract boolean isEmpty();

    public abstract ABoolExpr getDomainConstraint(AArithExpr expr);

    public AValue retrieveValue(Int value) {
        return value;
    }

}
