package lang.eventb.substitutions;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.True;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 00:27
 */
public final class Skip extends ASubstitution {

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public ABoolExpr getPrd(DefsContext defsContext) {
        return new True();
    }

}
