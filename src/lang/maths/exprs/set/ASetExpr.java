package lang.maths.exprs.set;

import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.bool.ABoolExpr;
import visitors.formatters.interfaces.IObjectFormattable;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:29
 */
public abstract class ASetExpr implements IObjectFormattable {

    public abstract boolean isEmpty();

    public abstract ABoolExpr getDomainConstraint(AArithExpr expr);

}
