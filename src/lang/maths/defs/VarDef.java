package lang.maths.defs;

import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.IExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 17:17
 */
public final class VarDef extends ADef {

    public VarDef(String name, ASetExpr domain) {
        super(name, domain);
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
