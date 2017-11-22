package lang.eventb.substitutions;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.Var;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.Equals;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 22:19
 */
public final class VarAssignment extends AAssignment<Var> {

    public VarAssignment(Var var, AArithExpr value) {
        super(var, value);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public ABoolExpr getPrd(DefsContext defsContext) {
        return null;
    }

    @Override
    ABoolExpr getPrdInAssignments(DefsContext defsContext) {
        return new Equals(assignable.prime(), value);
    }

}
