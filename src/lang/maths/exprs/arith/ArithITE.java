package lang.maths.exprs.arith;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.bool.ABoolExpr;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.IPrimer;
import visitors.formatters.interfaces.ISMTFormatter;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 18:37
 */
public final class ArithITE extends AArithExpr {

    private final ABoolExpr condition;
    private final AArithExpr thenPart;
    private final AArithExpr elsePart;

    public ArithITE(ABoolExpr condition, AArithExpr thenPart, AArithExpr elsePart) {
        this.condition = condition;
        this.thenPart = thenPart;
        this.elsePart = elsePart;
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
    public ArithITE accept(IPrimer primer) {
        return primer.visit(this);
    }

    @Override
    public LinkedHashSet<Const> getConsts() {
        return Stream.of(condition.getConsts(), thenPart.getConsts(), elsePart.getConsts()).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return Stream.of(condition.getVars(defsContext), thenPart.getVars(defsContext), elsePart.getVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<FunVar> getFunVars(DefsContext defsContext) {
        return Stream.of(condition.getFunVars(defsContext), thenPart.getFunVars(defsContext), elsePart.getFunVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<Fun> getFuns() {
        return Stream.of(condition.getFuns(), thenPart.getFuns(), elsePart.getFuns()).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    public ABoolExpr getCondition() {
        return condition;
    }

    public AArithExpr getThenPart() {
        return thenPart;
    }

    public AArithExpr getElsePart() {
        return elsePart;
    }

}
