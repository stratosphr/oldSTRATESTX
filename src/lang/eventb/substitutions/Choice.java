package lang.eventb.substitutions;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.bool.ABoolExpr;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.Arrays;
import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 19:36
 */
public final class Choice extends ASubstitution {

    private final LinkedHashSet<ASubstitution> substitutions;

    // TODO: CHECK IF PUTTING ASubstitution[] ALLOWS PUTTING NO SUBSTITUTION (IF SO, THIS CAN BE USED IN MANY OTHER CLASSES)
    public Choice(ASubstitution... substitutions) {
        this.substitutions = new LinkedHashSet<>(Arrays.asList(substitutions));
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public ABoolExpr getPrd(DefsContext defsContext) {
        return null;
    }

    public LinkedHashSet<ASubstitution> getSubstitutions() {
        return substitutions;
    }

}
