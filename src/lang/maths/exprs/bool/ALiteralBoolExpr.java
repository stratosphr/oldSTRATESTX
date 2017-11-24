package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.Const;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.FunVar;
import lang.maths.exprs.arith.Var;
import visitors.formatters.interfaces.IPrimer;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 18:13
 */
public abstract class ALiteralBoolExpr extends ABoolExpr {

    @Override
    public abstract ABoolExpr accept(IPrimer primer);

    @Override
    public final LinkedHashSet<Const> getConsts() {
        return new LinkedHashSet<>();
    }

    @Override
    public final LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return new LinkedHashSet<>();
    }

    @Override
    public LinkedHashSet<FunVar> getFunVars(DefsContext defsContext) {
        return new LinkedHashSet<>();
    }

    @Override
    public final LinkedHashSet<Fun> getFuns() {
        return new LinkedHashSet<>();
    }

}
