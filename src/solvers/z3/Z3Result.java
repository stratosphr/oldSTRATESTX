package solvers.z3;

import com.microsoft.z3.Status;
import lang.maths.exprs.bool.ABoolExpr;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 14:50
 */
public final class Z3Result {

    private final ABoolExpr expr;
    private final Status status;
    private final Model model;
    private boolean unsatCore;

    Z3Result(ABoolExpr expr, Status status, Model model) {
        this.expr = expr;
        this.status = status;
        this.model = model;
    }

    public boolean isSAT() {
        return status == Status.SATISFIABLE;
    }

    public boolean isUNSAT() {
        return status == Status.UNSATISFIABLE;
    }

    public boolean isUNKNOWN() {
        return status == Status.UNKNOWN;
    }

    public Model getModel() {
        if (!isSAT()) {
            throw new Error("Unable to generate a model for the following non satisfiable formula:\n" + expr);
        }
        return model;
    }

}
