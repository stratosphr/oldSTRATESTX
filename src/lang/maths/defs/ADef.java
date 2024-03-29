package lang.maths.defs;

import lang.AObject;
import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.ISMTFormattable;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 17:18
 */
public abstract class ADef<Domain extends ASetExpr> extends AObject implements ISMTFormattable {

    private final String name;
    final Domain domain;

    ADef(String name, Domain domain) {
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
