package visitors.formatters.interfaces;

import lang.maths.defs.FunDef;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.bool.And;
import lang.maths.exprs.bool.Equals;
import lang.maths.exprs.bool.In;
import lang.maths.exprs.bool.Or;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 01:52
 */
public interface IExprFormatter {

    String visit(FunDef funDef);

    String visit(VarDef varDef);

    String visit(Const aConst);

    String visit(Int anInt);

    String visit(Var var);

    String visit(Fun fun);

    String visit(Plus plus);

    String visit(Minus minus);

    String visit(Times times);

    String visit(Div div);

    String visit(Mod mod);

    String visit(ArithITE arithITE);

    String visit(Or or);

    String visit(And and);

    String visit(Equals equals);

    String visit(In in);

}
