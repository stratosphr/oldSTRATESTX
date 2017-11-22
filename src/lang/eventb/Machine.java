package lang.eventb;

import lang.AObject;
import lang.eventb.substitutions.ASubstitution;
import lang.maths.defs.DefsContext;
import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.set.ASetExpr;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 21:34
 */
public final class Machine extends AObject {

    private final String name;
    private final LinkedHashMap<String, AArithExpr> constsDefs;
    private final LinkedHashMap<String, ASetExpr> setsDefs;
    private final DefsContext defsContext;
    private final ABoolExpr invariant;
    private final ASubstitution initialisation;
    private final LinkedHashSet<Event> events;

    public Machine(String name, LinkedHashMap<String, AArithExpr> constsDefs, LinkedHashMap<String, ASetExpr> setsDefs, DefsContext defsContext, ABoolExpr invariant, ASubstitution initialisation, LinkedHashSet<Event> events) {
        this.name = name;
        this.constsDefs = constsDefs;
        this.setsDefs = setsDefs;
        this.defsContext = defsContext;
        this.invariant = invariant;
        this.initialisation = initialisation;
        this.events = events;
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    public String getName() {
        return name;
    }

    public LinkedHashMap<String, AArithExpr> getConstsDefs() {
        return constsDefs;
    }

    public LinkedHashMap<String, ASetExpr> getSetsDefs() {
        return setsDefs;
    }

    public DefsContext getDefsContext() {
        return defsContext;
    }

    public ABoolExpr getInvariant() {
        return invariant;
    }

    public ASubstitution getInitialisation() {
        return initialisation;
    }

    public LinkedHashSet<Event> getEvents() {
        return events;
    }

}
