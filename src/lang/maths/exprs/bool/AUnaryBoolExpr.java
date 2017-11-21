package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.AGenericTypeExpr;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.Var;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 15:05
 */
public abstract class AUnaryBoolExpr<T extends AGenericTypeExpr> extends ABoolExpr {

    private final T operand;

    AUnaryBoolExpr(T operand) {
        this.operand = operand;
    }

    @Override
    public final LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return operand.getVars(defsContext);
    }

    @Override
    public LinkedHashSet<Fun> getFuns(DefsContext defsContext) {
        return operand.getFuns(defsContext);
    }

    public T getOperand() {
        return operand;
    }

}
