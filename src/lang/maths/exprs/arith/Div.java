package lang.maths.exprs.arith;

import visitors.formatters.interfaces.IGenericExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:44
 */
public final class Div extends ANaryArithExpr<AArithExpr> {

    public Div(AArithExpr... operands) {
        super(operands);
    }

    @Override
    public String accept(IGenericExprFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

}
