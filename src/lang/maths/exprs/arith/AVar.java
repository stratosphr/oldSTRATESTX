package lang.maths.exprs.arith;

import visitors.formatters.interfaces.IPrimer;

/**
 * Created by gvoiron on 22/11/17.
 * Time : 01:04
 */
public abstract class AVar extends AAssignable {

    AVar(String unPrimedName, String primedName) {
        this(unPrimedName, primedName, false);
    }

    AVar(String unPrimedName, String primedName, boolean isPrimed) {
        super(unPrimedName, primedName, isPrimed);
    }

    @Override
    public abstract AVar accept(IPrimer primer);

}
