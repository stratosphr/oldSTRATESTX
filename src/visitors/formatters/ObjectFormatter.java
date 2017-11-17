package visitors.formatters;

import lang.eventb.substitutions.Skip;
import lang.exprs.arith.*;
import lang.exprs.bool.Equals;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.stream.Collectors;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 01:53
 */
public final class ObjectFormatter extends AFormatter implements IObjectFormatter {

    @Override
    public String visit(Int anInt) {
        return anInt.getValue().toString();
    }

    @Override
    public String visit(Var var) {
        return var.getName();
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
    public String visit(Equals equals) {
        return equals.getOperands().stream().map(operand -> operand.accept(this)).collect(Collectors.joining(" = "));
    }

    @Override
    public String visit(Skip skip) {
        return "SKIP";
    }

}
