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
public final class FunVar extends AVar {

    private final String funName;
    private final String parameter;

    public FunVar(String funName, String parameter) {
        this(funName, parameter, false);
    }

    public FunVar(String funName, String parameter, boolean isPrimed) {
        super(funName + "!" + parameter, funName + Primer.getSuffix() + "!" + parameter, isPrimed);
        this.funName = funName;
        this.parameter = parameter;
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
    public LinkedHashSet<AVar> getVars(DefsContext defsContext) {
        return new LinkedHashSet<>(Collections.singletonList(this));
    }

    @Override
    public LinkedHashSet<Fun> getFuns() {
        return new LinkedHashSet<>();
    }

    public String getFunName() {
        return funName;
    }

    public String getParameter() {
        return parameter;
    }

}
