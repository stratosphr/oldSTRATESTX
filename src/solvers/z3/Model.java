package solvers.z3;

import com.microsoft.z3.Context;
import com.microsoft.z3.FuncDecl;
import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.*;

import java.util.TreeMap;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 14:56
 */
@SuppressWarnings("WeakerAccess")
public final class Model extends TreeMap<AAssignable, AValue> {

    Model(com.microsoft.z3.Model model, Context context, DefsContext defsContext) {
        for (FuncDecl funcDecl : model.getConstDecls()) {
            String name = funcDecl.getName().toString();
            if (!name.contains("!") || name.endsWith("!")) {
                AValue value = defsContext.getVarsDefs().get(name).getDomain().retrieveValue(new Int(Integer.parseInt(model.eval(context.mkIntConst(name), true).toString())));
                put(new Var(name), value);
            } else if (name.contains("!")) {
                String[] split = name.split("!");
                String funName = split[0];
                Int parameter = new Int(Integer.parseInt(split[1]));
                if (defsContext.getFunsDefs().containsKey(funName)) {
                    AValue value = defsContext.getFunDef(funName).getCoDomain().retrieveValue(new Int(Integer.parseInt(model.eval(context.mkIntConst(name), true).toString())));
                    put(new Fun(funName, parameter), value);
                }
            }
        }
    }

}
