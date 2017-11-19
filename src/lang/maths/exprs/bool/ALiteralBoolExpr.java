package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.Var;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 18:13
 */
public abstract class ALiteralBoolExpr extends ABoolExpr {

    @Override
    public final LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return new LinkedHashSet<>();
    }

}
