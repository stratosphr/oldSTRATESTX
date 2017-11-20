package visitors.formatters.interfaces;

import lang.eventb.substitutions.Skip;
import lang.maths.defs.FunDef;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.bool.*;
import lang.maths.exprs.set.FiniteSet;
import lang.maths.exprs.set.usuals.*;

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

    String visit(True aTrue);

    String visit(False aFalse);

    String visit(Not not);

    String visit(Or or);

    String visit(And and);

    String visit(Equals equals);

    String visit(LT lt);

    String visit(LEQ leq);

    String visit(GEQ geq);

    String visit(GT gt);

    String visit(InDomain inDomain);

    String visit(Implies implies);

    String visit(ForAll forAll);

    String visit(Exists exists);

    String visit(Z z);

    String visit(ZMinus zMinus);

    String visit(ZMinusStar zMinusStar);

    String visit(ZMinusPlus zMinusPlus);

    String visit(N n);

    String visit(NPlus nPlus);

    String visit(FiniteSet set);

    String visit(Skip skip);

}
