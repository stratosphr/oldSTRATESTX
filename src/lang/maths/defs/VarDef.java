package lang.maths.defs;

import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.ISMTFormatter;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 17:17
 */
public final class VarDef<Domain extends ASetExpr> extends ADef<Domain> {

    public VarDef(String name, Domain domain) {
        super(name, domain);
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
