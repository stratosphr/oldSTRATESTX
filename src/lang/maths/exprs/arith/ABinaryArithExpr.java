package lang.maths.exprs.arith;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.AGenericTypeExpr;
import visitors.formatters.interfaces.IPrimer;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:44
 */
abstract class ABinaryArithExpr<Operand extends AGenericTypeExpr<Operand>> extends AArithExpr {

    private final Operand left;
    private final Operand right;

    ABinaryArithExpr(Operand left, Operand right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public abstract ABinaryArithExpr<Operand> accept(IPrimer primer);

    @Override
    public final LinkedHashSet<Const> getConsts() {
        return Stream.of(left.getConsts(), right.getConsts()).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public final LinkedHashSet<AVar> getVars(DefsContext defsContext) {
        return Stream.of(left.getVars(defsContext), right.getVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public final LinkedHashSet<Fun> getFuns() {
        return Stream.of(left.getFuns(), right.getFuns()).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    public Operand getLeft() {
        return left;
    }

    public Operand getRight() {
        return right;
    }

}
