package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.Var;
import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.IExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 14:09
 */
public final class InDomain extends ABoolExpr {

    private final AArithExpr expr;
    private final ASetExpr set;
    private final ABoolExpr constraint;

    public InDomain(AArithExpr expr, ASetExpr set) {
        this.expr = expr;
        this.set = set;
        this.constraint = set.getDomainConstraint(expr);
    }

    @Override
    public LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return expr.getVars(defsContext);
    }

    @Override
    public LinkedHashSet<Fun> getFuns(DefsContext defsContext) {
        return expr.getFuns(defsContext);
    }

    public AArithExpr getExpr() {
        return expr;
    }

    public ASetExpr getSet() {
        return set;
    }

    public final ABoolExpr getConstraint() {
        return constraint;
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IExprFormatter formatter) {
        return formatter.visit(this);
    }

}
