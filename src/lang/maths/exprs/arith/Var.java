package lang.maths.exprs.arith;

import lang.maths.defs.DefsContext;
import visitors.formatters.Primer;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.IPrimer;
import visitors.formatters.interfaces.ISMTFormatter;

import java.util.Collections;
import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:52
 */
public final class Var extends AVar {

    public Var(String name) {
        this(name, false);
    }

    public Var(String name, boolean isPrimed) {
        super(name, name + Primer.getSuffix(), isPrimed);
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
    public Var accept(IPrimer primer) {
        return primer.visit(this);
    }

    @Override
    public LinkedHashSet<AVar> getVars(DefsContext defsContext) {
        return new LinkedHashSet<>(Collections.singletonList(this));
    }

    @Override
    public LinkedHashSet<Fun> getFuns(DefsContext defsContext) {
        return new LinkedHashSet<>();
    }

}
