package lang.exprs.arith;

import visitors.formatters.interfaces.IExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:44
 */
public final class Times extends ANaryArithExpr<AArithExpr> {

    public Times(AArithExpr... operands) {
        super(operands);
    }

    @Override
    public String accept(IExprFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

}
