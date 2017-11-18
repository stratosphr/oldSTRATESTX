package lang.maths.exprs.arith;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.bool.Equals;
import solvers.z3.Z3;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 19:04
 */
public abstract class AValue extends AArithExpr {

    Integer value;

    AValue() {
        this(null);
    }

    AValue(Integer value) {
        this.value = value;
    }

    public final Integer getValue(DefsContext defsContext) {
        if (value == null) {
            Z3.checkSAT(new Equals(new Var("value!"), this), defsContext);
            throw new Error("Unhandled case of const value!");
        }
        return value;
    }

}
