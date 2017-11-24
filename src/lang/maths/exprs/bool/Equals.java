package lang.maths.exprs.bool;

import lang.maths.exprs.arith.AArithExpr;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.IPrimer;
import visitors.formatters.interfaces.ISMTFormatter;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:16
 */
public final class Equals extends ANaryBoolExpr<AArithExpr> {

    public Equals(AArithExpr... operands) {
        super(operands);
        if (operands.length < 2) {
            throw new Error("The minimum number of operands expected to instantiate a \"" + getClass().getSimpleName() + "\" object is 2 (" + operands.length + " given).");
        }
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
    public Equals accept(IPrimer primer) {
        return primer.visit(this);
    }

}
