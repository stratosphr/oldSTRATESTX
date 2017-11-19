package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.AGenericTypeExpr;
import lang.maths.exprs.arith.Var;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 14:54
 */
abstract class ABinaryBoolExpr<T extends AGenericTypeExpr> extends ABoolExpr {

    private final T left;
    private final T right;

    ABinaryBoolExpr(T left, T right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public final LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return Stream.of(left.getVars(defsContext), right.getVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    public T getLeft() {
        return left;
    }

    public T getRight() {
        return right;
    }

}
