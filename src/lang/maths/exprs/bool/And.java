package lang.maths.exprs.bool;

import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.IPrimer;
import visitors.formatters.interfaces.ISMTFormatter;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 12:50
 */
public final class And extends ANaryBoolExpr<ABoolExpr> {

    public And(ABoolExpr... operands) {
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

    @Override
    public And accept(IPrimer primer) {
        return primer.visit(this);
    }

}
