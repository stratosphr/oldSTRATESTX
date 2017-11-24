package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.AGenericTypeExpr;
import lang.maths.exprs.arith.Const;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.FunVar;
import lang.maths.exprs.arith.Var;
import visitors.formatters.interfaces.IPrimer;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 14:54
 */
abstract class ABinaryBoolExpr<Operand extends AGenericTypeExpr<Operand>> extends ABoolExpr {

    private final Operand left;
    private final Operand right;

    ABinaryBoolExpr(Operand left, Operand right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public abstract ABinaryBoolExpr<Operand> accept(IPrimer primer);

    @Override
    public final LinkedHashSet<Const> getConsts() {
        return Stream.of(left.getConsts(), right.getConsts()).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public final LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return Stream.of(left.getVars(defsContext), right.getVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<FunVar> getFunVars(DefsContext defsContext) {
        return Stream.of(left.getFunVars(defsContext), right.getFunVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public final LinkedHashSet<Fun> getFuns() {
        return Stream.of(left.getFuns(), right.getFuns()).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    public final Operand getLeft() {
        return left;
    }

    public final Operand getRight() {
        return right;
    }

}
