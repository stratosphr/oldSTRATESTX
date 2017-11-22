package lang.eventb.substitutions;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.AAssignable;
import lang.maths.exprs.bool.ABoolExpr;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 18:49
 */
public abstract class AAssignment<Assignable extends AAssignable> extends ASubstitution {

    final Assignable assignable;
    protected final AArithExpr value;

    AAssignment(Assignable assignable, AArithExpr value) {
        this.assignable = assignable;
        this.value = value;
    }

    public Assignable getAssignable() {
        return assignable;
    }

    public AArithExpr getValue() {
        return value;
    }

    abstract ABoolExpr getPrdInAssignments(DefsContext defsContext);

}
