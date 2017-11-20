package visitors.formatters.interfaces;

import parsers.xml.XMLNode;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 19:15
 */
public interface IXMLFormatter {

    String visit(XMLNode XMLNode);

}
