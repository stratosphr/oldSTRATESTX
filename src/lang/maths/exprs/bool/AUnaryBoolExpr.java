package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.AGenericTypeExpr;
import lang.maths.exprs.arith.Const;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.FunVar;
import lang.maths.exprs.arith.Var;
import visitors.formatters.interfaces.IPrimer;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 15:05
 */
public abstract class AUnaryBoolExpr<Operand extends AGenericTypeExpr<Operand>> extends ABoolExpr {

    private final Operand operand;

    AUnaryBoolExpr(Operand operand) {
        this.operand = operand;
    }

    @Override
    public abstract AUnaryBoolExpr<Operand> accept(IPrimer primer);

    @Override
    public final LinkedHashSet<Const> getConsts() {
        return operand.getConsts();
    }

    @Override
    public final LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return operand.getVars(defsContext);
    }

    @Override
    public LinkedHashSet<FunVar> getFunVars(DefsContext defsContext) {
        return operand.getFunVars(defsContext);
    }

    @Override
    public LinkedHashSet<Fun> getFuns() {
        return operand.getFuns();
    }

    public Operand getOperand() {
        return operand;
    }

}
