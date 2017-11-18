import lang.maths.defs.DefsContext;
import lang.maths.defs.FunDef;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.Int;
import lang.maths.exprs.arith.Var;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.Equals;
import lang.maths.exprs.set.Set;
import solvers.z3.Z3;
import solvers.z3.Z3Result;

public class Main {

    // TODO : HANDLE OR AND AND LOGICAL OPERATORS WITH NO PARAMETERS IN SMTFormatter
    public static void main(String[] args) {
        Var var0 = new Var("var0");
        Var var1 = new Var("var1");
        Fun fun0_0 = new Fun("fun0", new Int(0));
        Fun fun1_0 = new Fun("fun1", new Int(0));
        DefsContext defsContext = new DefsContext();
        defsContext.addDef(new VarDef(var0.getName(), new Set(new Int(1), new Int(-1))));
        defsContext.addDef(new VarDef(var1.getName(), new Set(new Int(1))));
        defsContext.addDef(new FunDef(fun0_0.getName(), new Set(new Int(0), new Int(1), new Int(2)), new Set(new Int(0), new Int(2), new Int(2))));
        defsContext.addDef(new FunDef(fun1_0.getName(), new Set(new Int(0), new Int(1), new Int(3)), new Set(new Int(1), new Int(2))));
        ABoolExpr expr = new Equals(fun0_0, var0);
        Z3Result result = Z3.checkSAT(expr, defsContext);
        if (result.isSAT()) {
            System.out.println(result.getModel());
        }
    }

}
