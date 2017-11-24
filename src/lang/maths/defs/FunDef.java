package lang.maths.defs;

import lang.maths.exprs.set.AFiniteSetExpr;
import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.ISMTFormatter;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:52
 */
public final class FunDef extends ADef<AFiniteSetExpr> {

    private final ASetExpr coDomain;

    public FunDef(String name, AFiniteSetExpr domain, ASetExpr coDomain) {
        super(name, domain);
        this.coDomain = coDomain;
    }

    @Override
    public String accept(ISMTFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public AFiniteSetExpr getDomain() {
        return domain;
    }

    public ASetExpr getCoDomain() {
        return coDomain;
    }

}
