package lang.maths.exprs.arith;

import lang.maths.defs.DefsContext;
import visitors.formatters.interfaces.IExprFormatter;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.Collections;
import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 21:52
 */
public final class Var extends AAssignable {

    private final String name;

    public Var(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    @Override
    public String accept(IExprFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public LinkedHashSet<Var> getVars(DefsContext defsContext) {
        return new LinkedHashSet<>(Collections.singletonList(this));
    }

}
