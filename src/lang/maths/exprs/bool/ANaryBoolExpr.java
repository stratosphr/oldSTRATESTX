package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.AGenericTypeExpr;
import lang.maths.exprs.arith.Const;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.FunVar;
import lang.maths.exprs.arith.Var;
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
