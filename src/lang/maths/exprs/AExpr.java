package lang.maths.exprs;

import lang.AObject;
import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.Const;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.FunVar;
import lang.maths.exprs.arith.Var;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 18:06
 */
public abstract class AExpr extends AObject {

    public abstract LinkedHashSet<Const> getConsts();

    public abstract LinkedHashSet<Var> getVars(DefsContext defsContext);

    public abstract LinkedHashSet<FunVar> getFunVars(DefsContext defsContext);

    public abstract LinkedHashSet<Fun> getFuns();

}
