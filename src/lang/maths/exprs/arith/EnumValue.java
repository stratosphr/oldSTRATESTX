package lang.maths.exprs.arith;

import lang.AObject;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.ISMTFormatter;

import java.util.LinkedHashMap;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 02:11
 */
public final class EnumValue extends AValue {

    private static final LinkedHashMap<String, Int> enumvalues = new LinkedHashMap<>();
    private final String name;

    public EnumValue(String name) {
        super(enumvalues.containsKey(name) ? enumvalues.get(name).getValue() : enumvalues.size());
        enumvalues.put(name, new Int(enumvalues.size()));
        this.name = name;
    }

    @Override
    public String accept(ISMTFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    public String getName() {
        return name;
    }

    @Override
    public int compareTo(AObject object) {
        return enumvalues.get(name).compareTo(enumvalues.get(((EnumValue) object).getName()));
    }

}
