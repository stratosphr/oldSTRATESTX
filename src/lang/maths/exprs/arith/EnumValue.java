package lang.maths.exprs.arith;

import lang.AObject;
import visitors.formatters.interfaces.IObjectFormatter;
import visitors.formatters.interfaces.IPrimer;
import visitors.formatters.interfaces.ISMTFormatter;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 02:11
 */
public final class EnumValue extends AValue {

    // TODO: FIND A WAY TO RESET enumValues WHEN CREATING A NEW MACHINE TO FREE MEMORY FROM USELESS EnumValues
    private static final LinkedHashMap<String, Int> enumValues = new LinkedHashMap<>();
    private final String name;

    public EnumValue(String name) {
        super(enumValues.containsKey(name) ? enumValues.get(name).getValue() : enumValues.size());
        if (!enumValues.containsKey(name)) {
            enumValues.put(name, new Int(enumValues.size()));
        }
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

    @Override
    public EnumValue accept(IPrimer primer) {
        return primer.visit(this);
    }

    @Override
    public LinkedHashSet<Const> getConsts() {
        return new LinkedHashSet<>();
    }

    public String getName() {
        return name;
    }

    @Override
    public int compareTo(AObject object) {
        return enumValues.get(name).compareTo(enumValues.get(((EnumValue) object).getName()));
    }

}
