package lang.maths.exprs.bool;

import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.IPrimer;
import visitors.formatters.interfaces.ISMTFormatter;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 11:21
 */
public final class Implies extends ABinaryBoolExpr<ABoolExpr> {

    public Implies(ABoolExpr condition, ABoolExpr thenPart) {
        super(condition, thenPart);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(ISMTFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public Implies accept(IPrimer primer) {
        return primer.visit(this);
    }

    public ABoolExpr getCondition() {
        return getLeft();
    }

    public ABoolExpr getThenPart() {
        return getRight();
    }

}
