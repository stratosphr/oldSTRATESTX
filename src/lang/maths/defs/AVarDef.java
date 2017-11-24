package lang.maths.defs;

import lang.maths.exprs.arith.AVar;
import lang.maths.exprs.set.ASetExpr;

/**
 * Created by gvoiron on 23/11/17.
 * Time : 01:18
 */
public abstract class AVarDef<Var extends AVar, Domain extends ASetExpr> extends ADef<Domain> {

    protected final Var var;

    AVarDef(Var var, Domain domain) {
        super(var.getName(), domain);
        this.var = var;
    }

    public abstract Var getVar();

}
