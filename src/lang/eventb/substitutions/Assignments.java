package lang.eventb.substitutions;

import lang.maths.defs.DefsContext;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.And;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.Arrays;
import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 18:47
 */
public class Assignments extends ASubstitution {

    private final LinkedHashSet<AAssignment> assignments;

    public Assignments(AAssignment... substitutions) {
        this.assignments = new LinkedHashSet<>(Arrays.asList(substitutions));
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public ABoolExpr getPrd(DefsContext defsContext) {
        return new And(assignments.stream().map(assignment -> assignment.getPrdInAssignments(defsContext)).toArray(ABoolExpr[]::new));
    }

    public LinkedHashSet<AAssignment> getAssignments() {
        return assignments;
    }

}
