import parsers.ebm.EBMParser;
import utilities.ResourcesManager;

import static utilities.ResourcesManager.EModel.EXAMPLE;

class Main {

    public static void main(String[] args) {
        EBMParser parser = new EBMParser();
        try {
            parser.parse(ResourcesManager.getModel(EXAMPLE));
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

}
