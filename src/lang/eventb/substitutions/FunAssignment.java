package lang.eventb.substitutions;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.Equals;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 22:20
 */
public class FunAssignment extends AAssignment<Fun> {

    public FunAssignment(Fun fun, AArithExpr value) {
        super(fun, value);
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
    public ABoolExpr getPrdInAssignments(DefsContext defsContext) {
        return new Equals(assignable.prime(), value);
    }

}
