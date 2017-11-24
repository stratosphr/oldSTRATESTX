package lang.maths.defs;

import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.Int;
import lang.maths.exprs.arith.Var;

import java.util.LinkedHashMap;

import static lang.maths.exprs.set.usuals.EUsualSet.Z;
import static lang.maths.exprs.set.usuals.UsualSetFabric.getUsualSet;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:36
 */
public final class DefsContext {

    private final LinkedHashMap<String, Int> constsDefs;
    private final LinkedHashMap<String, VarDef> varsDefs;
    private final LinkedHashMap<String, FunVarDef> funVarsDefs;
    private final LinkedHashMap<String, FunDef> funsDefs;

    public DefsContext() {
        this.constsDefs = new LinkedHashMap<>();
        this.varsDefs = new LinkedHashMap<>();
        this.funVarsDefs = new LinkedHashMap<>();
        this.funsDefs = new LinkedHashMap<>();
    }

    public void addFreshVar(Var var) {
        addDef(new VarDef<>(var, getUsualSet(Z)));
    }

    public void addConstDef(String name, Int value) {
        if (constsDefs.containsKey(name) && !constsDefs.get(name).equals(value)) {
            throw new Error("Error: const \"" + name + "\" was already defined in this scope.");
        }
        constsDefs.put(name, value);
    }

    public void addDef(VarDef varDef) {
        if (varsDefs.containsKey(varDef.getVar().getName()) && !varsDefs.get(varDef.getName()).equals(varDef)) {
            throw new Error("Error: variable \"" + varDef.getVar() + "\" was already defined in this scope (" + varsDefs.get(varDef.getVar().getName()) + ".");
        }
        if (varDef.getDomain().isEmpty(this)) {
            throw new Error("Error: the domain of variable \"" + varDef.getVar() + "\" cannot be empty.");
        }
        varsDefs.put(varDef.getVar().getName(), varDef);
    }

    private void addDef(FunVarDef funVarDef) {
        if (funVarsDefs.containsKey(funVarDef.getVar().getName()) && !funVarsDefs.get(funVarDef.getName()).equals(funVarDef)) {
            throw new Error("Error: variable \"" + funVarDef.getVar() + "\" was already defined in this scope (" + funVarsDefs.get(funVarDef.getVar().getName()) + ".");
        }
        if (funVarDef.getDomain().isEmpty(this)) {
            throw new Error("Error: the domain of variable \"" + funVarDef.getVar() + "\" cannot be empty.");
        }
        funVarsDefs.put(funVarDef.getVar().getName(), funVarDef);
    }

    public void addDef(FunDef funDef) {
        if (funsDefs.containsKey(funDef.getName()) && !funsDefs.get(funDef.getName()).equals(funDef)) {
            throw new Error("Error: function \"" + funDef.getName() + "\" was already defined in this scope.");
        }
        if (funDef.getDomain().isEmpty(this)) {
            throw new Error("Error: the domain of function \"" + funDef.getName() + "\" cannot be empty.");
        }
        if (funDef.getCoDomain().isEmpty(this)) {
            throw new Error("Error: the co-domainA of function \"" + funDef.getName() + "\" cannot be empty.");
        }
        funDef.getDomain().getElements().forEach(element -> addDef(new FunVarDef<>(new Fun(funDef.getName(), element).getFunVar(), funDef.getDomain())));
        funsDefs.put(funDef.getName(), funDef);
    }

    public LinkedHashMap<String, Int> getConstsDefs() {
        return constsDefs;
    }

    public LinkedHashMap<String, VarDef> getVarsDefs() {
        return varsDefs;
    }

    public LinkedHashMap<String, FunVarDef> getFunVarsDefs() {
        return funVarsDefs;
    }

    public LinkedHashMap<String, FunDef> getFunsDefs() {
        return funsDefs;
    }

}
