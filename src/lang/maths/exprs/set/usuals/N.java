package lang.maths.exprs.set.usuals;

import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.Int;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.GEQ;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 14:20
 */
public final class N extends AUsualSet {

    N() {
        super(new Int(0), null);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public ABoolExpr getDomainConstraint(AArithExpr expr) {
        return new GEQ(expr, new Int(0));
    }

}
