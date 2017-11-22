package lang.maths.exprs.arith;

import visitors.formatters.interfaces.IPrimer;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 00:15
 */
public abstract class AAssignable extends AArithExpr {

    private final String unPrimedName;
    private final String primedName;
    private final String realName;
    private final boolean isPrimed;

    AAssignable(String unPrimedName, String primedName) {
        this(unPrimedName, primedName, false);
    }

    AAssignable(String unPrimedName, String primedName, boolean isPrimed) {
        this.unPrimedName = unPrimedName;
        this.primedName = primedName;
        this.realName = isPrimed ? primedName : unPrimedName;
        this.isPrimed = isPrimed;
    }

    @Override
    public abstract AAssignable accept(IPrimer primer);

    public String getRealName() {
        return realName;
    }

    public String getUnPrimedName() {
        return unPrimedName;
    }

    public String getPrimedName() {
        return primedName;
    }

    public boolean isPrimed() {
        return isPrimed;
    }

}
