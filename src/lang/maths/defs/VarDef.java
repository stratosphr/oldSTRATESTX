package lang.maths.defs;

import lang.maths.exprs.arith.Var;
import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.ISMTFormatter;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 17:17
 */
public final class VarDef<Domain extends ASetExpr> extends AVarDef<Var, Domain> {

    public VarDef(Var var, Domain domain) {
        super(var, domain);
    }

    @Override
    public Var getVar() {
        return var;
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
