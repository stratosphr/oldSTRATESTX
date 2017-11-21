package lang.maths.exprs.bool;

import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.ISMTFormatter;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 18:10
 */
public final class True extends ALiteralBoolExpr {


    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(ISMTFormatter formatter) {
        return formatter.visit(this);
    }

}
