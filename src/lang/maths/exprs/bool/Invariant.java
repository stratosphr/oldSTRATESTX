package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AVar;
import lang.maths.exprs.arith.Fun;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.IPrimer;
import visitors.formatters.interfaces.ISMTFormatter;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 22/11/17.
 * Time : 02:06
 */
public final class Invariant extends ABoolExpr {

    private ABoolExpr expr;

    public Invariant(ABoolExpr expr) {
        this.expr = expr;
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
    public Invariant accept(IPrimer primer) {
        return primer.visit(this);
    }

    @Override
    public LinkedHashSet<AVar> getVars(DefsContext defsContext) {
        return expr.getVars(defsContext);
    }

    @Override
    public LinkedHashSet<Fun> getFuns(DefsContext defsContext) {
        return expr.getFuns(defsContext);
    }

    public ABoolExpr getExpr() {
        return expr;
    }

}
