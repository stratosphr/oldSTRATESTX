package lang.maths.defs;

import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.IExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:52
 */
public final class FunDef extends ADef {

    private final ASetExpr coDomain;

    public FunDef(String name, ASetExpr domain, ASetExpr coDomain) {
        super(name, domain);
        if (coDomain.isEmpty()) {
            throw new Error("Error: the co-domain of \"" + name + "\" cannot be empty.");
        }
        this.coDomain = coDomain;
    }

    @Override
    public String accept(IExprFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    public ASetExpr getCoDomain() {
        return coDomain;
    }

}
