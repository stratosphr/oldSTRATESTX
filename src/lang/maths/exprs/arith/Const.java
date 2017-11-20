package lang.maths.exprs.arith;

import visitors.formatters.interfaces.IGenericExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:14
 */
public final class Const extends AValue {

    private String name;

    public Const(String name) {
        this.name = name;
    }

    @Override
    public String accept(IGenericExprFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    public String getName() {
        return name;
    }

}
