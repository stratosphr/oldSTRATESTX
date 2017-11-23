package solvers.z3;

import com.microsoft.z3.Status;
import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AAssignable;
import lang.maths.exprs.bool.ABoolExpr;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 14:50
 */
public final class Z3Result {

    private final ABoolExpr expr;
    private final Status status;
    private final DefsContext defsContext;
    private final Model model;

    Z3Result(ABoolExpr expr, DefsContext defsContext, Status status, Model model) {
        this.expr = expr;
        this.status = status;
        this.defsContext = defsContext;
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
        return getModel(Stream.of(expr.getVars(defsContext), expr.getFuns()).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new)));
    }

    // TODO: THIS METHOD DOES NOT TAKE THE assignables INTO ACCOUNT FOR THE MOMENT
    public Model getModel(LinkedHashSet<AAssignable> assignables) {
        if (!isSAT()) {
            throw new Error("Unable to generate a model for the following non satisfiable formula:\n" + expr);
        }
        return model;
    }

}
