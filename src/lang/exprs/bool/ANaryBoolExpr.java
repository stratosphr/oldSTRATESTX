package lang.exprs.bool;

import lang.exprs.AExpr;

import java.util.Arrays;
import java.util.List;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:32
 */
abstract class ANaryBoolExpr<T extends AExpr> extends ABoolExpr {

    private final List<T> operands;

    ANaryBoolExpr(T[] operands) {
        if (operands.length < 2) {
            throw new Error("The minimum number of operands expected to instantiate a \"" + getClass().getSimpleName() + "\" object is 2 (only " + operands.length + " were given)");
        }
        this.operands = Arrays.asList(operands);
    }

    public List<T> getOperands() {
        return operands;
    }

}
