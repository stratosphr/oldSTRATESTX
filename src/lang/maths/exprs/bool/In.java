package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.Var;
import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.IExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 21:10
 */
public final class In extends ABoolExpr {

    private final AArithExpr expr;
    private final ASetExpr set;

    public In(AArithExpr expr, ASetExpr set) {
        this.expr = expr;
        this.set = set;
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IExprFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return expr.getVars(defsContext);
    }

    public AArithExpr getExpr() {
        return expr;
    }

    public ASetExpr getSet() {
        return set;
    }

}
