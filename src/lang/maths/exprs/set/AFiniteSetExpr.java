package lang.maths.exprs.set;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.AExpr;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.Equals;
import lang.maths.exprs.bool.Or;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.TreeSet;
import java.util.stream.Collectors;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:29
 */
public abstract class AFiniteSetExpr extends ASetExpr {

    public abstract TreeSet<? extends AArithExpr> getElements();

    @Override
    public ABoolExpr getDomainConstraint(AArithExpr expr) {
        return new Or(getElements().stream().map(value -> new Equals(expr, value)).toArray(ABoolExpr[]::new));
    }

    public final int size() {
        return getElements().size();
    }

    @Override
    public boolean isEmpty(DefsContext defsContext) {
        return getElements().isEmpty();
    }

    @Override
    public LinkedHashSet<Const> getConsts() {
        return getElements().stream().map(AExpr::getConsts).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return getElements().stream().map(expr -> expr.getVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<FunVar> getFunVars(DefsContext defsContext) {
        return getElements().stream().map(expr -> expr.getFunVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<Fun> getFuns() {
        return getElements().stream().map(AExpr::getFuns).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

}
