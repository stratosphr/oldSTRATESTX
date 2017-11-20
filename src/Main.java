import parsers.ebm.EBMParser;
import utilities.ResourcesManager;

import static utilities.ResourcesManager.EModel.*;

public class Main {

    public static void main(String[] args) {
        EBMParser parser = new EBMParser();
        parser.parse(ResourcesManager.getModel(CA));
        parser.parse(ResourcesManager.getModel(CM));
        parser.parse(ResourcesManager.getModel(EL));
        parser.parse(ResourcesManager.getModel(EV));
        parser.parse(ResourcesManager.getModel(GSM));
        parser.parse(ResourcesManager.getModel(L14));
        parser.parse(ResourcesManager.getModel(L14_2));
        parser.parse(ResourcesManager.getModel(PH));
    }

}
