package parsers.ebm;

import parsers.xml.XMLNode;
import parsers.xml.XMLParser;
import utilities.ResourcesManager;

import java.io.File;

import static utilities.ResourcesManager.EXMLSchema.EBM;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 16:06
 */
public final class EBMParser {

    public EBMParser() {
    }

    public void parse(File file) throws Exception {
        XMLParser xmlParser = new XMLParser(true);
        XMLNode root = xmlParser.parse(file, ResourcesManager.getXMLSchema(EBM));
        System.out.println(root);
        root.assertConformsTo("model", 3, 7, "sets-defs", "consts-defs", "vars-defs", "funs-defs", "invariant", "initialisation", "events");
    }

}
