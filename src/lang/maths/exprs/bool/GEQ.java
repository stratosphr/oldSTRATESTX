package lang.maths.exprs.bool;

import lang.maths.exprs.arith.AArithExpr;
import visitors.formatters.interfaces.IExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 14:53
 */
public final class GEQ extends ABinaryBoolExpr<AArithExpr> {

    public GEQ(AArithExpr left, AArithExpr right) {
        super(left, right);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IExprFormatter formatter) {
        return formatter.visit(this);
    }

}
