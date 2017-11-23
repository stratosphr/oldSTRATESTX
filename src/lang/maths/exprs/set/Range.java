package lang.maths.exprs.set;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.Int;
import lang.maths.exprs.arith.Var;
import lang.maths.exprs.bool.*;
import solvers.z3.Z3;
import solvers.z3.Z3Result;
import utilities.Maths;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.Collection;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 23:57
 */
public final class Range extends AFiniteSetExpr {

    private final AArithExpr lowerBound;
    private final AArithExpr upperBound;
    private TreeSet<AArithExpr> elements;

    public Range(AArithExpr lowerBound, AArithExpr upperBound) {
        this.lowerBound = lowerBound;
        this.upperBound = upperBound;
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public TreeSet<AArithExpr> getElements() {
        if (elements == null) {
            Var lowerBoundVar = new Var("lowerBound");
            Var upperBoundVar = new Var("upperBound");
            DefsContext defsContext = new DefsContext();
            Stream.of(lowerBound.getConsts(), upperBound.getConsts()).flatMap(Collection::stream).forEach(aConst -> defsContext.addConstDef(aConst.getName(), new Int(aConst.getValue())));
            defsContext.addFreshVar(lowerBoundVar);
            defsContext.addFreshVar(upperBoundVar);
            Z3Result result = Z3.checkSAT(new And(new Equals(lowerBoundVar, lowerBound), new Equals(upperBoundVar, upperBound)), defsContext);
            if (result.isSAT()) {
                elements = Maths.range(result.getModel().get(lowerBoundVar).getValue(), result.getModel().get(upperBoundVar).getValue()).stream().map(Int::new).collect(Collectors.toCollection(TreeSet::new));
            } else {
                throw new Error("Error: Unable to compute elements in range \"" + this + "\".");
            }
        }
        return elements;
    }

    @Override
    public boolean isEmpty(DefsContext defsContext) {
        return false;
    }

    @Override
    public ABoolExpr getDomainConstraint(AArithExpr expr) {
        return new And(new GEQ(expr, lowerBound), new LEQ(expr, upperBound));
    }

    public AArithExpr getLowerBound() {
        return lowerBound;
    }

    public AArithExpr getUpperBound() {
        return upperBound;
    }

}
