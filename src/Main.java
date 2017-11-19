import lang.maths.defs.DefsContext;
import lang.maths.defs.FunDef;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.Int;
import lang.maths.exprs.arith.Var;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.And;
import lang.maths.exprs.bool.Equals;
import lang.maths.exprs.set.FiniteSet;
import lang.maths.exprs.set.N;
import solvers.z3.Z3;
import solvers.z3.Z3Result;

public class Main {

    public static void main(String[] args) {

        Var var0 = new Var("var0");
        Var var1 = new Var("var1");
        Var var2 = new Var("var2");
        Fun fun0_0 = new Fun("fun0", var0);
        Fun fun0_1 = new Fun("fun0", var1);
        Fun fun0_2 = new Fun("fun0", var0);

        DefsContext defsContext = new DefsContext();
        defsContext.addDef(new VarDef<>(var0.getName(), new FiniteSet(new Int(0), new Int(-1))));
        defsContext.addDef(new VarDef<>(var1.getName(), new FiniteSet(new Int(1), new Int(-1))));
        defsContext.addDef(new VarDef<>(var2.getName(), new FiniteSet(new Int(2), new Int(-1))));
        defsContext.addDef(new FunDef(fun0_0.getName(), new FiniteSet(new Int(0), new Int(1)), new N()));

        ABoolExpr expr = new And(
                new Equals(fun0_0, new Int(0)),
                new Equals(fun0_1, new Int(1)),
                new Equals(fun0_2, new Int(2))
        );
        Z3Result result = Z3.checkSAT(expr, defsContext);
        if (result.isSAT()) {
            System.out.println(result.getModel());
        }

    }

}
