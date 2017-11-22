package lang.maths.exprs;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AVar;
import lang.maths.exprs.arith.Fun;
import visitors.formatters.Primer;
import visitors.formatters.interfaces.ISMTFormattable;
import visitors.formatters.interfaces.ISMTPrimable;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:13
 */
public abstract class AGenericTypeExpr<Prime extends AGenericTypeExpr> extends AExpr implements ISMTFormattable, ISMTPrimable<Prime> {

    public final Prime prime() {
        return accept(new Primer(true));
    }

    public abstract LinkedHashSet<AVar> getVars(DefsContext defsContext);

    public abstract LinkedHashSet<Fun> getFuns(DefsContext defsContext);

}
