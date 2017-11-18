package visitors.formatters;

import lang.eventb.substitutions.Skip;
import lang.maths.defs.FunDef;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.bool.And;
import lang.maths.exprs.bool.Equals;
import lang.maths.exprs.bool.In;
import lang.maths.exprs.bool.Or;
import lang.maths.exprs.set.Set;
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
    public String visit(In in) {
        return in.getExpr().accept(this) + " in " + in.getSet().accept(this);
    }

    @Override
    public String visit(Set set) {
        return "{" + set.getElements().stream().map(element -> element.accept(this)).collect(Collectors.joining(", ")) + "}";
    }

    @Override
    public String visit(Skip skip) {
        return "SKIP";
    }

}
