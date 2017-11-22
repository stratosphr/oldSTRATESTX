package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AVar;
import lang.maths.exprs.arith.Fun;
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
    public final LinkedHashSet<AVar> getVars(DefsContext defsContext) {
        return new LinkedHashSet<>();
    }

    @Override
    public final LinkedHashSet<Fun> getFuns(DefsContext defsContext) {
        return new LinkedHashSet<>();
    }

}
