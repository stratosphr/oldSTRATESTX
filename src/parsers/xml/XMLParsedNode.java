package parsers.xml;

import java.io.File;
import java.util.ArrayList;
import java.util.Map;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 15:21
 */
public final class XMLParsedNode extends AXMLNode<XMLParsedNode> {

    private final File file;
    private final int line;
    private final int column;

    XMLParsedNode(String name, File file, int line, int column) {
        super(name);
        this.file = file;
        this.line = line;
        this.column = column;
    }

    public XMLParsedNode(String name, Map<String, String> attributes, ArrayList<XMLParsedNode> children, File file, int line, int column) {
        super(name, attributes, children);
        this.file = file;
        this.line = line;
        this.column = column;
    }

    public File getFile() {
        return file;
    }

    public int getLine() {
        return line;
    }

    public int getColumn() {
        return column;
    }

}
