package solvers.z3;

import com.microsoft.z3.*;
import lang.maths.defs.DefsContext;
import lang.maths.exprs.bool.ABoolExpr;
import visitors.formatters.SMTFormatter2;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 12:29
 */
public final class Z3 {

    private final static Context context = new Context();
    private final static Solver solver = context.mkSolver();

    private Z3() {
    }

    public static Z3Result checkSAT(ABoolExpr expr, DefsContext defsContext) {
        solver.reset();
        String formattedExpr = new SMTFormatter2(defsContext).format(expr);
        try {
            BoolExpr assertion = context.parseSMTLIB2String(formattedExpr, null, null, null, null);
            solver.add(assertion);
        } catch (Z3Exception exception) {
            throw new Error(exception + "\nError while parsing the following code:\n" + formattedExpr);
        }
        Status status = solver.check();
        return new Z3Result(expr, defsContext, status, status == Status.SATISFIABLE ? new Model(solver.getModel(), context, defsContext) : null);
    }

}
