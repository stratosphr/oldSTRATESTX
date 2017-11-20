package lang.maths.exprs.set.usuals;

import lang.maths.exprs.arith.Int;
import lang.maths.exprs.set.AInfiniteSetExpr;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 10:48
 */
abstract class AUsualSet extends AInfiniteSetExpr {

    AUsualSet(Int lowerBound, Int upperBound, Int... excluded) {
        super(lowerBound, upperBound, excluded);
    }

}
