package lang.maths.exprs;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.Var;
import visitors.formatters.interfaces.IGenericExprFormattable;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:13
 */
public abstract class AGenericTypeExpr extends AExpr implements IGenericExprFormattable {

    public abstract LinkedHashSet<Var> getVars(DefsContext defsContext);

    public abstract LinkedHashSet<Fun> getFuns(DefsContext defsContext);

}
