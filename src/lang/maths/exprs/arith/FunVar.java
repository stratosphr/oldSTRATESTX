package lang.maths.exprs.arith;

import lang.maths.defs.DefsContext;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.IPrimer;
import visitors.formatters.interfaces.ISMTFormatter;

import java.util.Collections;
import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:52
 */
public final class FunVar extends AVar {

    private final Fun fun;

    public FunVar(Fun fun) {
        super(fun.getName() + "!" + fun.getParameter());
        this.fun = fun;
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
    public FunVar accept(IPrimer primer) {
        return primer.visit(this);
    }

    @Override
    public LinkedHashSet<Const> getConsts() {
        return new LinkedHashSet<>();
    }

    @Override
    public LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return new LinkedHashSet<>();
    }

    @Override
    public LinkedHashSet<FunVar> getFunVars(DefsContext defsContext) {
        return new LinkedHashSet<>(Collections.singletonList(this));
    }

    @Override
    public LinkedHashSet<Fun> getFuns() {
        return new LinkedHashSet<>();
    }

    public Fun getFun() {
        return fun;
    }

}
