package lang.maths.exprs.set;

import lang.maths.exprs.AExpr;
import lang.maths.exprs.arith.AValue;

import java.util.LinkedHashSet;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:29
 */
public abstract class ASetExpr extends AExpr {

    public abstract LinkedHashSet<AValue> getElements();

    public final int getCard() {
        return getElements().size();
    }

    public final boolean isEmpty() {
        return getElements().isEmpty();
    }

}
