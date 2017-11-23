package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.AGenericTypeExpr;
import lang.maths.exprs.arith.AVar;
import lang.maths.exprs.arith.Const;
import lang.maths.exprs.arith.Fun;
import visitors.formatters.interfaces.IPrimer;

import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:32
 */
public abstract class ANaryBoolExpr<Operand extends AGenericTypeExpr<Operand>> extends ABoolExpr {

    private final List<Operand> operands;

    ANaryBoolExpr(Operand[] operands) {
        if (operands.length < 1) {
            throw new Error("The minimum number of operands expected to instantiate a \"" + getClass().getSimpleName() + "\" object is 1 (only " + operands.length + " were given)");
        }
        this.operands = Arrays.asList(operands);
    }

    public List<Operand> getOperands() {
        return operands;
    }

    @Override
    public abstract ANaryBoolExpr<Operand> accept(IPrimer primer);

    @Override
    public final LinkedHashSet<Const> getConsts() {
        return operands.stream().map(AGenericTypeExpr::getConsts).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public final LinkedHashSet<AVar> getVars(DefsContext defsContext) {
        return operands.stream().map(operand -> operand.getVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public final LinkedHashSet<Fun> getFuns() {
        return operands.stream().map(AGenericTypeExpr::getFuns).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

}
