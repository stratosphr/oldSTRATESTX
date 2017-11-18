package lang.maths.defs;

import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.Var;

import java.util.LinkedHashMap;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:36
 */
public final class DefsContext {

    // TODO : IT IS MAYBE POSSIBLE TO COMBINE VARSDEFS AND FUNSDEFS INTO ONE SINGLE LinkedHashMap SINCE THERE SHOULD BE NO FUN NAMED THE SAME AS A VAR AND CONVERSELY
    private final LinkedHashMap<String, VarDef> varsDefs;
    private final LinkedHashMap<String, FunDef> funsDefs;

    public DefsContext() {
        this.varsDefs = new LinkedHashMap<>();
        this.funsDefs = new LinkedHashMap<>();
    }

    public VarDef getDef(Var var) {
        if (!varsDefs.containsKey(var.getName())) {
            throw new Error("Error: variable \"" + var + "\" was not defined in this scope.");
        }
        return varsDefs.get(var.getName());
    }

    public FunDef getDef(Fun fun) {
        if (!funsDefs.containsKey(fun.getName())) {
            throw new Error("Error: function \"" + fun + "\" was not defined in this scope.");
        }
        return funsDefs.get(fun.getName());
    }

    public void addDef(VarDef varDef) {
        varsDefs.put(varDef.getName(), varDef);
    }

    public void addDef(FunDef funDef) {
        funDef.getDomain().getElements().forEach(value -> addDef(new VarDef(funDef.getName() + "!" + value, funDef.getCoDomain())));
        funsDefs.put(funDef.getName(), funDef);
    }

}
