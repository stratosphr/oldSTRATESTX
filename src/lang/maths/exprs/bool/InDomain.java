package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.AVar;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.IPrimer;
import visitors.formatters.interfaces.ISMTFormatter;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 14:09
 */
public final class InDomain extends ABoolExpr {

    private final AArithExpr expr;
    private final ASetExpr domain;
    private final ABoolExpr constraint;

    public InDomain(AArithExpr expr, ASetExpr domain) {
        this.expr = expr;
        this.domain = domain;
        this.constraint = domain.getDomainConstraint(expr);
    }

    @Override
    public LinkedHashSet<AVar> getVars(DefsContext defsContext) {
        return expr.getVars(defsContext);
    }

    @Override
    public LinkedHashSet<Fun> getFuns(DefsContext defsContext) {
        return expr.getFuns(defsContext);
    }

    public AArithExpr getExpr() {
        return expr;
    }

    public ASetExpr getDomain() {
        return domain;
    }

    public final ABoolExpr getConstraint() {
        return constraint;
    }

    @Override
    public InDomain accept(IPrimer primer) {
        return primer.visit(this);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(ISMTFormatter formatter) {
        return formatter.visit(this);
    }

}
