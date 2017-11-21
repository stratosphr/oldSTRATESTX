package lang.maths.exprs.arith;

import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.ISMTFormatter;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:44
 */
public final class Plus extends ANaryArithExpr<AArithExpr> {

    public Plus(AArithExpr... operands) {
        super(operands);
    }

    @Override
    public String accept(ISMTFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

}
