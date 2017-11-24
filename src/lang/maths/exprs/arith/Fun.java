package lang.maths.exprs.arith;

import lang.AObject;
import lang.maths.defs.DefsContext;
import visitors.formatters.Primer;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.IPrimer;
import visitors.formatters.interfaces.ISMTFormatter;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:51
 */
public final class Fun extends AAssignable {

    private final AArithExpr parameter;

    public Fun(String name, AArithExpr parameter) {
        super(name);
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
    public Fun accept(IPrimer primer) {
        return primer.visit(this);
    }

    @Override
    public LinkedHashSet<Const> getConsts() {
        return parameter.getConsts();
    }

    @Override
    public LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return parameter.getVars(defsContext);
    }

    @Override
    public LinkedHashSet<FunVar> getFunVars(DefsContext defsContext) {
        return Stream.of(Arrays.asList(defsContext.getFunsDefs().get(accept(new Primer(false)).getName()).getDomain().getElements().stream().map(element -> new FunVar(this)).toArray(FunVar[]::new)), parameter.getFunVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<Fun> getFuns() {
        return new LinkedHashSet<>(Collections.singletonList(this));
    }

    public AArithExpr getParameter() {
        return parameter;
    }

    @Override
    public int compareTo(AObject object) {
        if (object instanceof Fun) {
            int comparison = getName().compareTo(((Fun) object).getName());
            if (comparison == 0) {
                return parameter.compareTo(((Fun) object).getParameter());
            } else {
                return comparison;
            }
        } else {
            return super.compareTo(object);
        }
    }

    public FunVar getFunVar() {
        return new FunVar(this);
    }

}
