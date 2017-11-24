package lang.maths.exprs.arith;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.AGenericTypeExpr;
import visitors.formatters.interfaces.IPrimer;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:44
 */
abstract class ANaryArithExpr<Operand extends AGenericTypeExpr<Operand>> extends AArithExpr {

    private final List<Operand> operands;

    ANaryArithExpr(Operand[] operands) {
        if (operands.length < 2) {
            throw new Error("The minimum number of operands expected to instantiate a \"" + getClass().getSimpleName() + "\" object is 2 (" + operands.length + " given).");
        }
        this.operands = Arrays.asList(operands);
    }

    public List<Operand> getOperands() {
        return operands;
    }

    @Override
    public abstract ANaryArithExpr<Operand> accept(IPrimer primer);

    @Override
    public final LinkedHashSet<Const> getConsts() {
        return operands.stream().map(AGenericTypeExpr::getConsts).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public final LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return operands.stream().map(operand -> operand.getVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<FunVar> getFunVars(DefsContext defsContext) {
        return operands.stream().map(operand -> operand.getFunVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public final LinkedHashSet<Fun> getFuns() {
        return operands.stream().map(AGenericTypeExpr::getFuns).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

}
