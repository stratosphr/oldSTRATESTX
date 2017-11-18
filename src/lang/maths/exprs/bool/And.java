package lang.maths.exprs.bool;

import visitors.formatters.interfaces.IExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 12:50
 */
public final class And extends ANaryBoolExpr<ABoolExpr> {

    public And(ABoolExpr... operands) {
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
