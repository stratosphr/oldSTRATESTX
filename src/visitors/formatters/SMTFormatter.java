package visitors.formatters;

import lang.exprs.arith.*;
import lang.exprs.bool.Equals;

import java.util.stream.Collectors;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 01:53
 */
public final class SMTFormatter extends AExprFormatter {

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
        return line("(+") + indentRight() + plus.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")");
    }

    @Override
    public String visit(Minus minus) {
        return line("(-") + indentRight() + minus.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")");
    }

    @Override
    public String visit(Times times) {
        return line("(*") + indentRight() + times.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")");
    }

    @Override
    public String visit(Div div) {
        return line("(/") + indentRight() + div.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")");
    }

    @Override
    public String visit(Mod mod) {
        return line("(mod") + indentRight() + mod.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")");
    }

    @Override
    public String visit(Equals equals) {
        return line("(=") + indentRight() + equals.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")");
    }

}
