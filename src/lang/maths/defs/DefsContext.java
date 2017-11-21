package lang.maths.defs;

import lang.maths.exprs.arith.Int;

import java.util.LinkedHashMap;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:36
 */
public final class DefsContext {

    private final LinkedHashMap<String, Int> constsDefs;
    private final LinkedHashMap<String, VarDef> varsDefs;
    private final LinkedHashMap<String, FunDef> funsDefs;

    public DefsContext() {
        this.constsDefs = new LinkedHashMap<>();
        this.varsDefs = new LinkedHashMap<>();
        this.funsDefs = new LinkedHashMap<>();
    }

    public void addDef(String name, Int value) {
        if (constsDefs.containsKey(name)) {
            throw new Error("Error: const \"" + name + "\" was already defined in this scope.");
        }
        constsDefs.put(name, value);
    }

    public void addDef(VarDef varDef) {
        if (varsDefs.containsKey(varDef.getName())) {
            throw new Error("Error: variable \"" + varDef.getName() + "\" was already defined in this scope.");
        }
        varsDefs.put(varDef.getName(), varDef);
    }

    public void addDef(FunDef funDef) {
        if (funsDefs.containsKey(funDef.getName())) {
            throw new Error("Error: function \"" + funDef.getName() + "\" was already defined in this scope.");
        }
        funDef.getDomain().getElements().forEach(value -> addDef(new VarDef<>(funDef.getName() + "!" + value, funDef.getCoDomain())));
        funsDefs.put(funDef.getName(), funDef);
    }

    public LinkedHashMap<String, Int> getConstsDefs() {
        return constsDefs;
    }

    public LinkedHashMap<String, VarDef> getVarsDefs() {
        return varsDefs;
    }

    public LinkedHashMap<String, FunDef> getFunsDefs() {
        return funsDefs;
    }

}
