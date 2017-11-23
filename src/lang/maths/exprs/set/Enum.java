package lang.maths.exprs.set;

import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.AValue;
import lang.maths.exprs.arith.EnumValue;
import lang.maths.exprs.arith.Int;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 01:53
 */
public final class Enum extends AFiniteSetExpr {

    private final TreeSet<EnumValue> enumValues;
    private final LinkedHashMap<Int, EnumValue> enumValuesMapping;

    public Enum(EnumValue... enumValues) {
        this.enumValues = new TreeSet<>(Arrays.asList(enumValues));
        this.enumValuesMapping = new LinkedHashMap<>(Arrays.stream(enumValues).collect(Collectors.toMap(enumValue -> new Int(enumValue.getValue()), Function.identity())));
        //Arrays.stream(enumValues).forEach(enumValue -> enumValuesMapping.put(new Int(enumValue.getValue()), enumValue));
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public TreeSet<? extends AArithExpr> getElements() {
        return enumValues;
    }

    @Override
    public AValue retrieveValue(Int value) {
        if (enumValuesMapping.containsKey(value)) {
            return enumValuesMapping.get(value);
        } else {
            throw new Error("Error: enum value \"" + value + "\" is not a valid enum value in set " + this + ".");
        }
    }

}
