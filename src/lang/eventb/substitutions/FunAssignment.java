package lang.eventb.substitutions;

import lang.maths.defs.DefsContext;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.Var;
import lang.maths.exprs.bool.*;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.Arrays;
import java.util.Collection;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 22:20
 */
public class FunAssignment extends AAssignment<Fun> {

    public FunAssignment(Fun fun, AArithExpr value) {
        super(fun, value);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public ABoolExpr getPrd(DefsContext defsContext) {
        return new And(
                Stream.of(
                        Arrays.asList(
                                getPrdInAssignments(defsContext),
                                new ForAll(
                                        new Implies(
                                                new NotEquals(new Var("i!"), assignable.getParameter()),
                                                new Equals(new Fun(assignable.getUnPrimedName(), assignable.getParameter()).prime(), new Fun(assignable.getUnPrimedName(), assignable.getParameter()))
                                        ),
                                        new VarDef<>(new Var("i!"), defsContext.getFunsDefs().get(assignable.getUnPrimedName()).getDomain())
                                )
                        ),
                        defsContext.getVarsDefs().values().stream().map(varDef -> new Equals(varDef.getVar().prime(), varDef.getVar())).collect(Collectors.toList()),
                        defsContext.getFunVarsDefs().values().stream().filter(funVarDef -> !funVarDef.getVar().getFunName().equals(assignable.getUnPrimedName())).map(funVarDef -> new Equals(funVarDef.getVar().prime(), funVarDef.getVar())).collect(Collectors.toList())
                ).flatMap(Collection::stream).toArray(ABoolExpr[]::new)
        );
    }

    @Override
    public ABoolExpr getPrdInAssignments(DefsContext defsContext) {
        return new And(
                new InDomain(getAssignable().getParameter(), defsContext.getFunsDefs().get(assignable.getUnPrimedName()).getDomain()),
                new InDomain(value, defsContext.getFunsDefs().get(assignable.getUnPrimedName()).getCoDomain()),
                new Equals(assignable.prime(), value)
        );
    }

}
