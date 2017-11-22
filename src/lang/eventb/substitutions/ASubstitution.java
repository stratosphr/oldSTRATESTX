package lang.eventb.substitutions;

import lang.AObject;
import lang.maths.defs.DefsContext;
import lang.maths.exprs.bool.ABoolExpr;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 00:27
 */
public abstract class ASubstitution extends AObject {

    public abstract ABoolExpr getPrd(DefsContext defsContext);

}
