package lang.maths.exprs.arith;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.AGenericTypeExpr;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:44
 */
abstract class ANaryArithExpr<T extends AGenericTypeExpr> extends AArithExpr {

    private final List<T> operands;

    ANaryArithExpr(T[] operands) {
        if (operands.length < 2) {
            throw new Error("The minimum number of operands expected to instantiate a \"" + getClass().getSimpleName() + "\" object is 2 (only " + operands.length + " were given)");
        }
        this.operands = Arrays.asList(operands);
    }

    public List<T> getOperands() {
        return operands;
    }

    @Override
    public final LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return operands.stream().map(operand -> operand.getVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public final LinkedHashSet<Fun> getFuns(DefsContext defsContext) {
        return operands.stream().map(operand -> operand.getFuns(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

}
