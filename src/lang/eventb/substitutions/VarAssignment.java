package lang.eventb.substitutions;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.Var;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.And;
import lang.maths.exprs.bool.Equals;
import lang.maths.exprs.bool.InDomain;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.Collection;
import java.util.Collections;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 22:19
 */
public final class VarAssignment extends AAssignment<Var> {

    public VarAssignment(Var var, AArithExpr value) {
        super(var, value);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public ABoolExpr getPrd(DefsContext defsContext) {
        return new And(
                Stream.of(
                        Collections.singletonList(getPrdInAssignments(defsContext)),
                        defsContext.getVarsDefs().values().stream().filter(varDef -> !varDef.getVar().equals(assignable)).map(varDef -> new Equals(varDef.getVar().prime(), varDef.getVar())).collect(Collectors.toList()),
                        defsContext.getFunVarsDefs().values().stream().map(funVarDef -> new Equals(funVarDef.getVar().prime(), funVarDef.getVar())).collect(Collectors.toList())
                ).flatMap(Collection::stream).toArray(ABoolExpr[]::new)
        );
    }

    @Override
    ABoolExpr getPrdInAssignments(DefsContext defsContext) {
        return new And(
                new InDomain(value, defsContext.getVarsDefs().get(assignable.getUnPrimedName()).getDomain()), new Equals(assignable.prime(), value)
        );
    }

}
