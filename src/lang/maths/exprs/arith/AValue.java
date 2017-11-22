package lang.maths.exprs.arith;

import lang.maths.defs.DefsContext;
import visitors.formatters.interfaces.IPrimer;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 19:04
 */
public abstract class AValue extends AArithExpr {

    private final int value;

    AValue(int value) {
        this.value = value;
    }

    public final Integer getValue() {
        return value;
    }

    @Override
    public abstract AValue accept(IPrimer primer);

    @Override
    public final LinkedHashSet<AVar> getVars(DefsContext defsContext) {
        return new LinkedHashSet<>();
    }

    @Override
    public final LinkedHashSet<Fun> getFuns(DefsContext defsContext) {
        return new LinkedHashSet<>();
    }

}
