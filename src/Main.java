import lang.eventb.Machine;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.AVar;
import parsers.ebm.EBMParser;
import utilities.ResourcesManager;
import visitors.formatters.Primer;

import java.util.stream.Collectors;

import static utilities.ResourcesManager.EModel.EXAMPLE;

class Main {

    public static void main(String[] args) {
        EBMParser parser = new EBMParser();
        try {
            Machine machine = parser.parse(ResourcesManager.getModel(EXAMPLE));
            for (AVar var : machine.getDefsContext().getVarsDefs().values().stream().map(VarDef::getVar).collect(Collectors.toList())) {
                AVar primedVar = var.accept(new Primer(true));
                System.out.println(var.getUnPrimedName() + ", " + var.getPrimedName() + ", " + var.getRealName());
                System.out.println(primedVar.getUnPrimedName() + ", " + primedVar.getPrimedName() + ", " + primedVar.getRealName());
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

}
