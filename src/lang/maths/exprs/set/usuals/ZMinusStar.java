package lang.maths.exprs.set.usuals;

import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.Int;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.LEQ;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 14:20
 */
public final class ZMinusStar extends AUsualSet {

    ZMinusStar() {
        super(null, new Int(0));
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public ABoolExpr getDomainConstraint(AArithExpr expr) {
        return new LEQ(expr, new Int(0));
    }

}
