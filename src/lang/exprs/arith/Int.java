package lang.exprs.arith;

import visitors.formatters.interfaces.IExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:14
 */
public final class Int extends AArithExpr {

    private final Integer value;

    public Int(int value) {
        this.value = value;
    }

    public Integer getValue() {
        return value;
    }

    @Override
    public String accept(IExprFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

}
