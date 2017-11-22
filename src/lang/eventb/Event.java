package lang.eventb;

import lang.AObject;
import lang.eventb.substitutions.ASubstitution;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 22:12
 */
public final class Event extends AObject {

    private final String name;
    private final ASubstitution substitution;

    public Event(String name, ASubstitution substitution) {
        this.name = name;
        this.substitution = substitution;
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    public String getName() {
        return name;
    }

    public ASubstitution getSubstitution() {
        return substitution;
    }

}
