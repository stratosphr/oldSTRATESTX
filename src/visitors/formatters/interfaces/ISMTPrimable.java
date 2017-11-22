package visitors.formatters.interfaces;

import lang.maths.exprs.AGenericTypeExpr;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 23:03
 */
public interface ISMTPrimable<Prime extends AGenericTypeExpr> {

    Prime accept(IPrimer primer);

}
