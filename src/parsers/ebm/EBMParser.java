package parsers.ebm;

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

    public void parse(File file) {
        XMLParser xmlParser = new XMLParser(true);
        xmlParser.parse(file, ResourcesManager.getXMLSchema(EBM));
    }

}
