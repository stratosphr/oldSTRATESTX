package lang.maths.exprs.bool;

import lang.maths.defs.DefsContext;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.Const;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.FunVar;
import lang.maths.exprs.arith.Var;
import visitors.formatters.interfaces.IPrimer;

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.stream.Collectors;

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
    public abstract AQuantifier accept(IPrimer primer);

    @Override
    public LinkedHashSet<Const> getConsts() {
        return expr.getConsts();
    }

    @Override
    public final LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return expr.getVars(defsContext).stream().filter(var -> varDefs.stream().noneMatch(varDef -> varDef.getVar().equals(var))).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<FunVar> getFunVars(DefsContext defsContext) {
        return expr.getFunVars(defsContext);
    }

    @Override
    public final LinkedHashSet<Fun> getFuns() {
        return expr.getFuns();
    }

    public final ABoolExpr getExpr() {
        return expr;
    }

    public final LinkedHashSet<VarDef> getQuantifiedVarsDefs() {
        return varDefs;
    }

}
