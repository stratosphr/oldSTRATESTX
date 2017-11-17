package visitors.formatters.interfaces;

import lang.exprs.arith.*;
import lang.exprs.bool.Equals;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 01:52
 */
public interface IExprFormatter {

    String visit(Int anInt);

    String visit(Var var);

    String visit(Plus plus);

    String visit(Minus minus);

    String visit(Times times);

    String visit(Div div);

    String visit(Mod mod);

    String visit(Equals equals);

}
