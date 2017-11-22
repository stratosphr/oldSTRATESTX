package lang.maths.exprs.arith;

import visitors.formatters.Primer;
import visitors.formatters.interfaces.IPrimer;

/**
 * Created by gvoiron on 19/11/17.
 * Time : 00:15
 */
public abstract class AAssignable extends AArithExpr {

    private final String unPrimedName;
    private final boolean isPrimed;
    private final String primedName;
    private final String realName;

    AAssignable(String unPrimedName) {
        this(unPrimedName, false);
    }

    AAssignable(String unPrimedName, boolean isPrimed) {
        this.unPrimedName = unPrimedName;
        this.isPrimed = isPrimed;
        this.primedName = unPrimedName + Primer.getSuffix();
        this.realName = isPrimed ? primedName : unPrimedName;
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
