package lang.eventb.substitutions;

import lang.maths.defs.DefsContext;
import lang.maths.defs.VarDef;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.And;
import lang.maths.exprs.bool.Exists;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.Arrays;
import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 19:43
 */
public final class Any extends ASubstitution {

    private final ABoolExpr condition;
    private final ASubstitution substitution;
    private final LinkedHashSet<VarDef> quantifiedVarsDefs;

    public Any(ABoolExpr condition, ASubstitution substitution, VarDef... quantifiedVarsDefs) {
        this.condition = condition;
        this.substitution = substitution;
        this.quantifiedVarsDefs = new LinkedHashSet<>(Arrays.asList(quantifiedVarsDefs));
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public ABoolExpr getPrd(DefsContext defsContext) {
        return new Exists(new And(condition, substitution.getPrd(defsContext)), quantifiedVarsDefs.toArray(new VarDef[0]));
    }

    public ASubstitution getSubstitution() {
        return substitution;
    }

    public ABoolExpr getCondition() {
        return condition;
    }

    public LinkedHashSet<VarDef> getQuantifiedVarsDefs() {
        return quantifiedVarsDefs;
    }

}
