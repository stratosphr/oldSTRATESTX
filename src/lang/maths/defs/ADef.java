package lang.maths.defs;

import lang.AObject;
import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.ISMTFormattable;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 17:18
 */
public abstract class ADef<Domain extends ASetExpr> extends AObject implements ISMTFormattable {

    private String unPrimedName;
    final Domain domain;

    ADef(String unPrimedName, Domain domain) {
        if (domain.isEmpty()) {
            throw new Error("Error: the domain of \"" + unPrimedName + "\" cannot be empty.");
        }
        this.unPrimedName = unPrimedName;
        this.domain = domain;
    }

    public String getUnPrimedName() {
        return unPrimedName;
    }

    public Domain getDomain() {
        return domain;
    }

}
