package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.AGenericTypeExpr;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.Var;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:32
 */
public abstract class ANaryBoolExpr<T extends AGenericTypeExpr> extends ABoolExpr {

    private final List<T> operands;

    ANaryBoolExpr(T[] operands) {
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
