package lang.maths.exprs.set;

import lang.maths.exprs.arith.AArithExpr;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.TreeSet;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 16:36
 */
public final class NamedSet extends AFiniteSetExpr {

    public NamedSet(String name) {
        super();
        throw new Error("Nothing is handled yet with NamedSet");
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return null;
    }

    @Override
    public TreeSet<? extends AArithExpr> getElements() {
        return null;
    }

}
