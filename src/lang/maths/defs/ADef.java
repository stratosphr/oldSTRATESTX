package lang.maths.defs;

import lang.AObject;
import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.IGenericExprFormattable;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 17:18
 */
public abstract class ADef<Domain extends ASetExpr> extends AObject implements IGenericExprFormattable {

    private final String name;
    final Domain domain;

    ADef(String name, Domain domain) {
        if (domain.isEmpty()) {
            throw new Error("Error: the domain of \"" + name + "\" cannot be empty.");
        }
        this.name = name;
        this.domain = domain;
    }

    public String getName() {
        return name;
    }

    public Domain getDomain() {
        return domain;
    }

}
