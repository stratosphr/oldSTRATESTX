package lang.maths.defs;

import lang.maths.exprs.arith.FunVar;
import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.ISMTFormatter;

/**
 * Created by gvoiron on 23/11/17.
 * Time : 01:14
 */
public final class FunVarDef<Domain extends ASetExpr> extends AVarDef<FunVar, Domain> {

    public FunVarDef(FunVar funVar, Domain domain) {
        super(funVar, domain);
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
    public FunVar getVar() {
        return var;
    }

}
