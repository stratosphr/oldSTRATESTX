package lang.maths.exprs.bool;

import lang.maths.exprs.AGenericTypeExpr;
import visitors.formatters.interfaces.IPrimer;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:17
 */
public abstract class ABoolExpr extends AGenericTypeExpr<ABoolExpr> {

    @Override
    public abstract ABoolExpr accept(IPrimer primer);

}
