package lang.maths.defs;

import java.util.LinkedHashMap;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:36
 */
public final class DefsContext {

    private final LinkedHashMap<String, ADef> defs;
    private final LinkedHashMap<String, VarDef> varsDefs;
    private final LinkedHashMap<String, FunDef> funsDefs;

    public DefsContext() {
        this.defs = new LinkedHashMap<>();
        this.varsDefs = new LinkedHashMap<>();
        this.funsDefs = new LinkedHashMap<>();
    }

    public ADef getDef(String name) {
        if (!defs.containsKey(name)) {
            throw new Error("Error: assignable \"" + name + "\" was not defined in this scope.");
        }
        return defs.get(name);
    }

    public void addDef(VarDef varDef) {
        if (defs.containsKey(varDef.getName())) {
            throw new Error("Error: variable \"" + varDef.getName() + "\" was already defined in this scope.");
        }
        varsDefs.put(varDef.getName(), varDef);
        defs.put(varDef.getName(), varDef);
    }

    public void addDef(FunDef funDef) {
        if (defs.containsKey(funDef.getName())) {
            throw new Error("Error: function \"" + funDef.getName() + "\" was already defined in this scope.");
        }
        funDef.getDomain().getElements().forEach(value -> addDef(new VarDef<>(funDef.getName() + "!" + value, funDef.getCoDomain())));
        funsDefs.put(funDef.getName(), funDef);
        defs.put(funDef.getName(), funDef);
    }

    public LinkedHashMap<String, ADef> getDefs() {
        return defs;
    }

    public LinkedHashMap<String, VarDef> getVarsDefs() {
        return varsDefs;
    }

    public LinkedHashMap<String, FunDef> getFunsDefs() {
        return funsDefs;
    }

}
