package lang.maths.exprs.arith;

import lang.maths.exprs.AGenericTypeExpr;
import visitors.formatters.interfaces.IPrimer;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:17
 */
public abstract class AArithExpr extends AGenericTypeExpr<AArithExpr> {

    @Override
    public abstract AArithExpr accept(IPrimer primer);

}
