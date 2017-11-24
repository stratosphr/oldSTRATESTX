package lang.maths.exprs;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.Const;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.FunVar;
import lang.maths.exprs.arith.Var;
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

    public abstract LinkedHashSet<Const> getConsts();

    public abstract LinkedHashSet<Var> getVars(DefsContext defsContext);

    public abstract LinkedHashSet<FunVar> getFunVars(DefsContext defsContext);

    public abstract LinkedHashSet<Fun> getFuns();

}
