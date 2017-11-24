import lang.eventb.Machine;
import lang.maths.exprs.arith.EnumValue;
import lang.maths.exprs.arith.Fun;
import lang.maths.exprs.arith.Int;
import lang.maths.exprs.arith.Var;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.And;
import lang.maths.exprs.bool.Equals;
import parsers.ebm.EBMParser;
import solvers.z3.Z3;
import solvers.z3.Z3Result;
import utilities.ResourcesManager;

import static utilities.ResourcesManager.EModel.EXAMPLE;

class Main {

    public static void main(String[] args) {
        EBMParser parser = new EBMParser();
        try {
            Machine machine = parser.parse(ResourcesManager.getModel(EXAMPLE));
            ABoolExpr constraint = new And(
                    machine.getInvariant(),
                    machine.getInvariant().prime(),
                    new And(new Equals(new Var("sw"), new Int(1))),
                    new And(new Equals(new Fun("bat", new Int(1)), new EnumValue("ok"))),
                    new And(new Equals(new Fun("bat", new Int(2)), new EnumValue("ok"))),
                    new And(new Equals(new Fun("bat", new Int(3)), new EnumValue("ok"))),
                    machine.getEvents().get("Commute").getSubstitution().getPrd(machine.getDefsContext())
            );
            Z3Result result = Z3.checkSAT(constraint, machine.getDefsContext());
            if (result.isSAT()) {
                System.out.println(result.getModel());
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

}
