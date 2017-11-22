package lang.maths.exprs.bool;

import lang.maths.exprs.arith.AArithExpr;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.IPrimer;
import visitors.formatters.interfaces.ISMTFormatter;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 22:03
 */
public final class NotEquals extends ABinaryBoolExpr<AArithExpr> {

    public NotEquals(AArithExpr left, AArithExpr right) {
        super(left, right);
    }

    @Override
    public String accept(ISMTFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public NotEquals accept(IPrimer primer) {
        return primer.visit(this);
    }

}
