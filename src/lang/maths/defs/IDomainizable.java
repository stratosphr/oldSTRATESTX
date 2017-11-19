package lang.maths.defs;

import lang.maths.exprs.set.AFiniteSetExpr;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:28
 */
public interface IDomainizable {

    AFiniteSetExpr getDomain(DefsContext defsContext);

}
