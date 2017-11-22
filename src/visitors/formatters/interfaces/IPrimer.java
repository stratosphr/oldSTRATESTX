package visitors.formatters.interfaces;

import lang.maths.exprs.arith.*;
import lang.maths.exprs.bool.*;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 23:05
 */
public interface IPrimer {

    Int visit(Int anInt);

    Const visit(Const aConst);

    EnumValue visit(EnumValue enumValue);

    Var visit(Var var);

    FunVar visit(FunVar funVar);

    Fun visit(Fun fun);

    Plus visit(Plus plus);

    Minus visit(Minus minus);

    Times visit(Times times);

    Div visit(Div div);

    Mod visit(Mod mod);

    False visit(False aFalse);

    True visit(True aTrue);

    Not visit(Not not);

    And visit(And and);

    Or visit(Or or);

    Equals visit(Equals equals);

    NotEquals visit(NotEquals notEquals);

    LT visit(LT lt);

    LEQ visit(LEQ leq);

    GEQ visit(GEQ geq);

    GT visit(GT gt);

    Implies visit(Implies implies);

    ArithITE visit(ArithITE arithITE);

    InDomain visit(InDomain inDomain);

    ForAll visit(ForAll forAll);

    Exists visit(Exists exists);

    Invariant visit(Invariant invariant);

}
