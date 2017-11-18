package lang.maths.exprs.set;

import lang.maths.exprs.arith.AValue;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.Arrays;
import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 17:33
 */
public final class Set extends ASetExpr {

    private LinkedHashSet<AValue> elements;

    public Set(AValue... elements) {
        this.elements = new LinkedHashSet<>(Arrays.asList(elements));
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public LinkedHashSet<AValue> getElements() {
        return elements;
    }

}
