package lang.maths.exprs.bool;

import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.Var;
import visitors.formatters.interfaces.IExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.Arrays;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 10:09
 */
public final class ForAll extends AQuantifier {

    public ForAll(ABoolExpr expr, VarDef... varDefs) {
        super(new Implies(new And(Arrays.stream(varDefs).map(varDef -> new InDomain(new Var(varDef.getName()), varDef.getDomain())).toArray(ABoolExpr[]::new)), expr), varDefs);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IExprFormatter formatter) {
        return formatter.visit(this);
    }

}
