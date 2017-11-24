package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.IPrimer;
import visitors.formatters.interfaces.ISMTFormatter;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 14:09
 */
public final class InDomain extends ABoolExpr {

    private final AArithExpr expr;
    private final ASetExpr domain;

    public InDomain(AArithExpr expr, ASetExpr domain) {
        this.expr = expr;
        this.domain = domain;
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

    @Override
    public LinkedHashSet<Const> getConsts() {
        return Stream.of(expr.getConsts(), domain.getConsts()).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return Stream.of(expr.getVars(defsContext), domain.getVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<FunVar> getFunVars(DefsContext defsContext) {
        return Stream.of(expr.getFunVars(defsContext), domain.getFunVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<Fun> getFuns() {
        return Stream.of(expr.getFuns(), domain.getFuns()).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    public AArithExpr getExpr() {
        return expr;
    }

    public ASetExpr getDomain() {
        return domain;
    }

    public final ABoolExpr getConstraint() {
        return domain.getDomainConstraint(expr);
    }

}
