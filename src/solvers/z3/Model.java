package solvers.z3;

import com.microsoft.z3.Context;
import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AAssignable;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.Int;
import lang.maths.exprs.arith.Var;

import java.util.TreeMap;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 14:56
 */
final class Model extends TreeMap<AAssignable, Int> {

    Model(com.microsoft.z3.Model model, Context context, DefsContext defsContext) {
        defsContext.getVarsDefs().keySet().forEach(name -> {
            if (!name.contains("!")) {
                put(new Var(name), new Int(Integer.parseInt(model.eval(context.mkIntConst(name), true).toString())));
            } else {
                String[] split = name.split("!");
                String funName = split[0];
                Int parameter = new Int(Integer.parseInt(split[1]));
                put(new Fun(funName, parameter), new Int(new Integer(model.eval(context.mkIntConst(name), true).toString())));
            }
        });
    }

}
