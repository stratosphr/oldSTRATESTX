package parsers.xml;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by gvoiron on 16/11/17.
 * Time : 17:59
 */
public abstract class AXMLNode<T extends AXMLNode<T>> {

    private T parent;
    private final String name;
    private final Map<String, String> attributes;
    private final List<T> children;
    private final StringBuilder text;

    AXMLNode(String name) {
        this(name, new HashMap<>(), new ArrayList<>());
    }

    AXMLNode(String name, Map<String, String> attributes, List<T> children) {
        this.parent = null;
        this.name = name;
        this.attributes = attributes;
        this.children = children;
        this.text = new StringBuilder();
    }

    final T getParent() {
        return parent;
    }

    @SuppressWarnings("WeakerAccess")
    void setParent(T parent) {
        this.parent = parent;
    }

    public final String getName() {
        return name;
    }

    public final Map<String, String> getAttributes() {
        return attributes;
    }

    void addAttribute(String name, String value) {
        attributes.put(name, value);
    }

    void addText(String text) {
        this.text.append(text);
    }

    public final List<T> getChildren() {
        return children;
    }

    void addChild(T child) {
        child.setParent(child);
        children.add(child);
    }

    @Override
    public String toString() {
        StringBuilder formatted = new StringBuilder("<" + name);
        if (!attributes.isEmpty()) {
            attributes.forEach((name, value) -> formatted.append(" ").append(name).append("=\"").append(value).append("\""));
        }
        if (!children.isEmpty()) {
            formatted.append(">\n");
            if (!text.toString().isEmpty()) {
                formatted.append(text).append("\n");
            }
            for (AXMLNode<T> child : children) {
                formatted.append(child.toString()).append("\n");
            }
            formatted.append("</").append(name).append(">");
        } else {
            formatted.append("/>");
        }
        return formatted.toString();
    }

}
