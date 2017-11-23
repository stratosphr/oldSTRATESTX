import lang.eventb.Machine;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.And;
import parsers.ebm.EBMParser;
import solvers.z3.Z3;
import solvers.z3.Z3Result;
import utilities.ResourcesManager;
import visitors.formatters.SMTFormatter2;

import static utilities.ResourcesManager.EModel.EXAMPLE;

class Main {

    public static void main(String[] args) {
        EBMParser parser = new EBMParser();
        try {
            Machine machine = parser.parse(ResourcesManager.getModel(EXAMPLE));
            ABoolExpr constraint = new And(
                    machine.getInvariant(),
                    machine.getInvariant().prime(),
                    machine.getEvents().get("Tic").getSubstitution().getPrd(machine.getDefsContext())
            );
            System.out.println(constraint);
            System.out.println(constraint.accept(new SMTFormatter2(machine.getDefsContext())));
            Z3Result result = Z3.checkSAT(constraint, machine.getDefsContext());
            if (result.isSAT()) {
                System.out.println(result.getModel());
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

}
