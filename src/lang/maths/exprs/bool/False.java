package lang.maths.exprs.bool;

import visitors.formatters.interfaces.IExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 18:12
 */
public final class False extends ALiteralBoolExpr {

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IExprFormatter formatter) {
        return formatter.visit(this);
    }

}
