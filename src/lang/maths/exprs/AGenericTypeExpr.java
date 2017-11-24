package lang.maths.exprs;

import visitors.formatters.Primer;
import visitors.formatters.interfaces.ISMTFormattable;
import visitors.formatters.interfaces.ISMTPrimable;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:13
 */
public abstract class AGenericTypeExpr<Prime extends AGenericTypeExpr> extends AExpr implements ISMTFormattable, ISMTPrimable<Prime> {

    public final Prime prime() {
        return accept(new Primer(true));
    }

}
