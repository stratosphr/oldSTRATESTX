import parsers.ebm.EBMParser;
import utilities.ResourcesManager;

import static utilities.ResourcesManager.EModel.EL;

public class Main {

    public static void main(String[] args) {
        EBMParser parser = new EBMParser();
        try {
            parser.parse(ResourcesManager.getModel(EL));
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

}
