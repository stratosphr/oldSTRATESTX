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
        this(name, parameter, false);
    }

    public Fun(String name, AArithExpr parameter, boolean isPrimed) {
        super(name, name + Primer.getSuffix(), isPrimed);
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
    public LinkedHashSet<AVar> getVars(DefsContext defsContext) {
        return Stream.of(Arrays.asList(defsContext.getFunsDefs().get(getUnPrimedName()).getDomain().getElements().stream().map(element -> new Fun(getUnPrimedName(), element, isPrimed()).getFunVar()).toArray(FunVar[]::new)), parameter.getVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
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
            int comparison = getRealName().compareTo(((Fun) object).getUnPrimedName());
            if (comparison == 0) {
                return parameter.compareTo(((Fun) object).getParameter());
            } else {
                return comparison;
            }
        } else {
            return super.compareTo(object);
        }
    }

    private FunVar getFunVar() {
        return new FunVar(getUnPrimedName(), parameter.toString(), isPrimed());
    }

}
