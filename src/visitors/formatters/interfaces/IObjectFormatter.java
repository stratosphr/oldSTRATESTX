package visitors.formatters.interfaces;

import lang.eventb.substitutions.Skip;
import lang.maths.defs.FunDef;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.bool.And;
import lang.maths.exprs.bool.Equals;
import lang.maths.exprs.bool.In;
import lang.maths.exprs.bool.Or;
import lang.maths.exprs.set.Set;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 01:50
 */
public interface IObjectFormatter {

    String visit(VarDef varDef);

    String visit(FunDef funDef);

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

    String visit(Set set);

    String visit(Skip skip);

}
