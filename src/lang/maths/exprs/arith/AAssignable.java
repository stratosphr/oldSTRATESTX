package lang.maths.exprs.arith;

import visitors.formatters.interfaces.IPrimer;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 00:15
 */
public abstract class AAssignable extends AArithExpr {

    private final String name;

    AAssignable(String name) {
        this.name = name;
    }

    @Override
    public abstract AAssignable accept(IPrimer primer);

    public String getName() {
        return name;
    }

}
