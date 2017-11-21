package lang.maths.exprs.set;

import lang.maths.exprs.arith.AArithExpr;
import lang.maths.exprs.arith.EnumValue;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.Arrays;
import java.util.TreeSet;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 01:53
 */
public final class Enum extends AFiniteSetExpr {

    private final TreeSet<AArithExpr> enumValues;

    public Enum(EnumValue... enumValues) {
        this.enumValues = new TreeSet<>(Arrays.asList(enumValues));
    }

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

    @Override
    public TreeSet<AArithExpr> getElements() {
        return enumValues;
    }

}
