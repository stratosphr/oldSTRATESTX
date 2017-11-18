package lang.maths.defs;

import lang.AObject;
import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.IGenericExprFormattable;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 17:18
 */
public abstract class ADef extends AObject implements IGenericExprFormattable {

    private final String name;
    private final ASetExpr domain;

    ADef(String name, ASetExpr domain) {
        if (domain.isEmpty()) {
            throw new Error("Error: the definition domain of \"" + name + "\" cannot be empty.");
        }
        this.name = name;
        this.domain = domain;
    }

    public String getName() {
        return name;
    }

    public ASetExpr getDomain() {
        return domain;
    }

}
