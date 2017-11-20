package lang.maths.exprs.bool;

import visitors.formatters.interfaces.IGenericExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 14:49
 */
public final class Not extends AUnaryBoolExpr<ABoolExpr> {

    public Not(ABoolExpr operand) {
        super(operand);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IGenericExprFormatter formatter) {
        return formatter.visit(this);
    }

}
