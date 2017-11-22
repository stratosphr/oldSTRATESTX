package lang.eventb.substitutions;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.And;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 19:08
 */
public final class Select extends ASubstitution {

    private final ABoolExpr condition;
    private final ASubstitution substitution;

    public Select(ABoolExpr condition, ASubstitution substitution) {
        this.condition = condition;
        this.substitution = substitution;
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public ABoolExpr getPrd(DefsContext defsContext) {
        return new And(condition, substitution.getPrd(defsContext));
    }

    public ABoolExpr getCondition() {
        return condition;
    }

    public ASubstitution getSubstitution() {
        return substitution;
    }

}
