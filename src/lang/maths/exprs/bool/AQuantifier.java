package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.Var;

import java.util.Arrays;
import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 10:09
 */
public abstract class AQuantifier extends ABoolExpr {

    private final ABoolExpr expr;
    private final LinkedHashSet<VarDef> varDefs;

    AQuantifier(ABoolExpr expr, VarDef... varDefs) {
        if (varDefs.length == 0) {
            throw new Error("The number of quantified variables for a " + getClass().getSimpleName() + " expression must be greater than 0.");
        }
        this.expr = expr;
        this.varDefs = new LinkedHashSet<>(Arrays.asList(varDefs));
    }

    @Override
    public final LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return expr.getVars(defsContext);
    }

    @Override
    public final LinkedHashSet<Fun> getFuns(DefsContext defsContext) {
        return expr.getFuns(defsContext);
    }

    public final ABoolExpr getExpr() {
        return expr;
    }

    public final LinkedHashSet<VarDef> getQuantifiedVarsDefs() {
        return varDefs;
    }

}
