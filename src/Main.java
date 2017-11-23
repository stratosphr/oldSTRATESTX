import lang.eventb.Machine;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.And;
import parsers.ebm.EBMParser;
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
                    machine.getEvents().get("Repair").getSubstitution().getPrd(machine.getDefsContext())
            );
            System.out.println(constraint);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

}
