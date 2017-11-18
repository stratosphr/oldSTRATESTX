package lang.maths.defs;

import lang.maths.exprs.set.ASetExpr;

/**
 * Created by gvoiron on 18/11/17.
 * Time : 16:21
 */
public interface ICoDomainizable extends IDomainizable {

    ASetExpr getCoDomain(DefsContext defsContext);

}
