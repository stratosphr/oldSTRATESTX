package lang.maths.exprs.set;

import lang.maths.defs.DefsContext;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.Const;
import lang.maths.exprs.arith.Int;
import lang.maths.exprs.arith.Var;
import lang.maths.exprs.bool.And;
import lang.maths.exprs.bool.Equals;
import lang.maths.exprs.set.usuals.UsualSetFabric;
import solvers.z3.Z3;
import solvers.z3.Z3Result;
import utilities.Maths;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.TreeSet;
import java.util.stream.Collectors;

import static lang.maths.exprs.set.usuals.EUsualSet.Z;

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

    // TODO : MAKE TWO DefsContext.addDef ACCEPTING A Var AND A Const RESPECTIVELY INSTEAD OF addDef(String, Int) TO RESPECTIVELY MAKE DECLARATION OF FRESH VARIABLES IN Z DOMAIN AUTOMATIC AND AVOID CONST CASTS IN THE FOLLOWING METHOD
    @Override
    public TreeSet<AArithExpr> getElements() {
        if (elements == null) {
            Var lowerBoundVar = new Var("lowerBound");
            Var upperBoundVar = new Var("upperBound");
            DefsContext defsContext = new DefsContext();
            if (lowerBound instanceof Const) {
                defsContext.addDef(((Const) lowerBound).getName(), new Int(((Const) lowerBound).getValue()));
            }
            if (upperBound instanceof Const) {
                defsContext.addDef(((Const) upperBound).getName(), new Int(((Const) upperBound).getValue()));
            }
            defsContext.addDef(new VarDef<>(lowerBoundVar.getName(), UsualSetFabric.getUsualSet(Z)));
            defsContext.addDef(new VarDef<>(upperBoundVar.getName(), UsualSetFabric.getUsualSet(Z)));
            Z3Result result = Z3.checkSAT(new And(new Equals(lowerBoundVar, lowerBound), new Equals(upperBoundVar, upperBound)), defsContext);
            if (result.isSAT()) {
                Integer lowerBoundValue = result.getModel().get(lowerBoundVar).getValue();
                Integer upperBoundValue = result.getModel().get(upperBoundVar).getValue();
                elements = Maths.range(lowerBoundValue, upperBoundValue).stream().map(Int::new).collect(Collectors.toCollection(TreeSet::new));
            }
        }
        return elements;
    }

    public AArithExpr getLowerBound() {
        return lowerBound;
    }

    public AArithExpr getUpperBound() {
        return upperBound;
    }

}
