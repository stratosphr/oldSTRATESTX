package lang.maths.exprs.arith;

import lang.AObject;
import lang.maths.defs.DefsContext;
import visitors.formatters.interfaces.IObjectFormatter;
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

    private final String name;
    private final AArithExpr parameter;

    public Fun(String name, AArithExpr parameter) {
        this.name = name;
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
    public LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return Stream.of(Arrays.asList(defsContext.getFunsDefs().get(name).getDomain().getElements().stream().map(value -> new Var(name + "!" + value)).toArray(Var[]::new)), parameter.getVars(defsContext)).flatMap(Collection::stream).collect(Collectors.toCollection(LinkedHashSet::new));
    }

    @Override
    public LinkedHashSet<Fun> getFuns(DefsContext defsContext) {
        return new LinkedHashSet<>(Collections.singletonList(this));
    }

    public String getName() {
        return name;
    }

    public AArithExpr getParameter() {
        return parameter;
    }

    @Override
    public int compareTo(AObject object) {
        if (object instanceof Fun) {
            int comparison = name.compareTo(((Fun) object).getName());
            if (comparison == 0) {
                return parameter.compareTo(((Fun) object).getParameter());
            } else {
                return comparison;
            }
        } else {
            return super.compareTo(object);
        }
    }

}
