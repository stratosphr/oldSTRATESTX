package visitors.formatters;

import lang.eventb.substitutions.Skip;
import lang.maths.defs.FunDef;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.bool.*;
import lang.maths.exprs.set.*;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.stream.Collectors;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 01:53
 */
public final class ObjectFormatter extends AFormatter implements IObjectFormatter {

    @Override
    public String visit(VarDef varDef) {
        return varDef.getName() + " in " + varDef.getDomain().accept(this);
    }

    @Override
    public String visit(FunDef funDef) {
        return funDef.getName() + " : " + funDef.getDomain().accept(this) + " -> " + funDef.getCoDomain().accept(this);
    }

    @Override
    public String visit(Const aConst) {
        return aConst.getName();
    }

    @Override
    public String visit(Int anInt) {
        return anInt.getValue().toString();
    }

    @Override
    public String visit(Var var) {
        return var.getName();
    }

    @Override
    public String visit(Fun fun) {
        return fun.getName() + "(" + fun.getParameter().accept(this) + ")";
    }

    @Override
    public String visit(Plus plus) {
        return plus.getOperands().stream().map(operand -> operand.accept(this)).collect(Collectors.joining(" + "));
    }

    @Override
    public String visit(Minus minus) {
        return minus.getOperands().stream().map(operand -> operand.accept(this)).collect(Collectors.joining(" - "));
    }

    @Override
    public String visit(Times times) {
        return times.getOperands().stream().map(operand -> operand instanceof Int || operand instanceof Var || operand instanceof Times ? operand.accept(this) : "(" + operand.accept(this) + ")").collect(Collectors.joining(" * "));
    }

    @Override
    public String visit(Div div) {
        return div.getOperands().stream().map(operand -> operand instanceof Int || operand instanceof Var || operand instanceof Div ? operand.accept(this) : "(" + operand.accept(this) + ")").collect(Collectors.joining(" / "));
    }

    @Override
    public String visit(Mod mod) {
        return mod.getOperands().stream().map(operand -> operand instanceof Int || operand instanceof Var || operand instanceof Mod ? operand.accept(this) : "(" + operand.accept(this) + ")").collect(Collectors.joining(" % "));
    }

    @Override
    public String visit(ArithITE arithITE) {
        return "(" + arithITE.getCondition().accept(this) + " ? " + arithITE.getThenPart().accept(this) + " : " + arithITE.getElsePart().accept(this) + ")";
    }

    @Override
    public String visit(True aTrue) {
        return "true";
    }

    @Override
    public String visit(False aFalse) {
        return "false";
    }

    @Override
    public String visit(Not not) {
        return "not(" + not.getOperand();
    }

    @Override
    public String visit(Or or) {
        return "or(" + or.getOperands().stream().map(operand -> operand.accept(this)).collect(Collectors.joining(", ")) + ")";
    }

    @Override
    public String visit(And and) {
        return "and(" + and.getOperands().stream().map(operand -> operand.accept(this)).collect(Collectors.joining(", ")) + ")";
    }

    @Override
    public String visit(Equals equals) {
        return equals.getOperands().stream().map(operand -> operand.accept(this)).collect(Collectors.joining(" = "));
    }

    @Override
    public String visit(LT lt) {
        return lt.getLeft() + " < " + lt.getRight();
    }

    @Override
    public String visit(LEQ leq) {
        return leq.getLeft() + " <= " + leq.getRight();
    }

    @Override
    public String visit(GEQ geq) {
        return geq.getLeft() + " >= " + geq.getRight();
    }

    @Override
    public String visit(GT gt) {
        return gt.getLeft() + " > " + gt.getRight();
    }

    @Override
    public String visit(AInDomain aInDomain) {
        return aInDomain.getExpr().accept(this) + " in " + aInDomain.getSet().accept(this);
    }

    @Override
    public String visit(Z z) {
        return "Z";
    }

    @Override
    public String visit(ZMinus zMinus) {
        return "Z-";
    }

    @Override
    public String visit(ZMinusStar zMinusStar) {
        return "Z-*";
    }

    @Override
    public String visit(ZMinusPlus zMinusPlus) {
        return "Z-+";
    }

    @Override
    public String visit(N n) {
        return "N";
    }

    @Override
    public String visit(NPlus nPlus) {
        return "N+";
    }

    @Override
    public String visit(FiniteSet set) {
        return "{" + set.getElements().stream().map(element -> element.accept(this)).collect(Collectors.joining(", ")) + "}";
    }

    @Override
    public String visit(Skip skip) {
        return "SKIP";
    }

}
