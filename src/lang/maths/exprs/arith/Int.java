package lang.maths.exprs.arith;

import lang.AObject;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.IPrimer;
import visitors.formatters.interfaces.ISMTFormatter;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:14
 */
public final class Int extends AValue {

    public Int(int value) {
        super(value);
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
    public Int accept(IPrimer primer) {
        return primer.visit(this);
    }

    @Override
    public int compareTo(AObject object) {
        return getValue().compareTo(((Int) object).getValue());
    }

}
