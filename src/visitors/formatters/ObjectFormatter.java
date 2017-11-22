package visitors.formatters;

import lang.eventb.Event;
import lang.eventb.Machine;
import lang.eventb.substitutions.*;
import lang.maths.defs.ADef;
import lang.maths.defs.FunDef;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.bool.*;
import lang.maths.exprs.set.Enum;
import lang.maths.exprs.set.Range;
import lang.maths.exprs.set.Set;
import lang.maths.exprs.set.usuals.*;
import visitors.formatters.interfaces.IObjectFormatter;

import java.util.stream.Collectors;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 01:53
 */
public final class ObjectFormatter extends AFormatter implements IObjectFormatter {

    @Override
    public String visit(VarDef varDef) {
        return varDef.getUnPrimedName() + " in " + varDef.getDomain().accept(this);
    }

    @Override
    public String visit(FunDef funDef) {
        return funDef.getUnPrimedName() + " : " + funDef.getDomain().accept(this) + " -> " + funDef.getCoDomain().accept(this);
    }

    @Override
    public String visit(Const aConst) {
        return aConst.getName() + "[" + aConst.getValue() + "]";
    }

    @Override
    public String visit(Int anInt) {
        return anInt.getValue().toString();
    }

    @Override
    public String visit(EnumValue enumValue) {
        return enumValue.getName() + "[" + enumValue.getValue() + "]";
    }

    @Override
    public String visit(Var var) {
        return var.getRealName();
    }

    @Override
    public String visit(FunVar funVar) {
        return funVar.getRealName();
    }

    @Override
    public String visit(Fun fun) {
        return fun.getRealName() + "(" + fun.getParameter().accept(this) + ")";
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
        return times.getOperands().stream().map(operand -> operand instanceof Int || operand instanceof Const || operand instanceof Var || operand instanceof Times ? operand.accept(this) : "(" + operand.accept(this) + ")").collect(Collectors.joining(" * "));
    }

    @Override
    public String visit(Div div) {
        return div.getOperands().stream().map(operand -> operand instanceof Int || operand instanceof Const || operand instanceof Var || operand instanceof Div ? operand.accept(this) : "(" + operand.accept(this) + ")").collect(Collectors.joining(" / "));
    }

    @Override
    public String visit(Mod mod) {
        return "(" + mod.getLeft() + " % " + mod.getRight() + ")";
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
    public String visit(NotEquals notEquals) {
        return notEquals.getLeft() + " ≠ " + notEquals.getRight();
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
    public String visit(InDomain inDomain) {
        return inDomain.getExpr().accept(this) + " in " + inDomain.getDomain().accept(this);
    }

    @Override
    public String visit(Implies implies) {
        return implies.getCondition() + " => " + implies.getThenPart();
    }

    @Override
    public String visit(ForAll forAll) {
        return "\\-/(" + forAll.getQuantifiedVarsDefs().stream().map(ADef::getUnPrimedName).collect(Collectors.joining(", ")) + ").(" + forAll.getExpr().accept(this) + ")";
    }

    @Override
    public String visit(Exists exists) {
        return "E(" + exists.getQuantifiedVarsDefs().stream().map(ADef::getUnPrimedName).collect(Collectors.joining(", ")) + ").(" + exists.getExpr().accept(this) + ")";
    }

    @Override
    public String visit(Invariant invariant) {
        return invariant.getExpr().accept(this);
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
    public String visit(Set set) {
        return "{" + set.getElements().stream().map(element -> element.accept(this)).collect(Collectors.joining(", ")) + "}";
    }

    @Override
    public String visit(Enum anEnum) {
        return "{" + anEnum.getElements().stream().map(element -> element.accept(this)).collect(Collectors.joining(", ")) + "}";
    }

    @Override
    public String visit(Range range) {
        return range.getLowerBound().accept(this) + ".." + range.getUpperBound().accept(this);
    }

    @Override
    public String visit(Machine machine) {
        String formatted = line("MACHINE \"" + machine.getName() + "\"");
        formatted += machine.getConstsDefs().isEmpty() ? "" : line() + indentRight() + indentLine("CONSTS") + indentRight() + machine.getConstsDefs().keySet().stream().map(name -> indentLine(name + " = " + machine.getConstsDefs().get(name).accept(this) + "[" + machine.getDefsContext().getConstsDefs().get(name).getValue() + "]")).collect(Collectors.joining()) + indentLeft() + indentLeft();
        formatted += machine.getSetsDefs().isEmpty() ? "" : line() + indentRight() + indentLine("SETS") + indentRight() + machine.getSetsDefs().keySet().stream().map(name -> indentLine(name + " = " + machine.getSetsDefs().get(name))).collect(Collectors.joining()) + indentLeft() + indentLeft();
        formatted += machine.getDefsContext().getVarsDefs().isEmpty() ? "" : line() + indentRight() + indentLine("VARS") + indentRight() + machine.getDefsContext().getVarsDefs().keySet().stream().map(name -> indentLine(machine.getDefsContext().getVarsDefs().get(name).accept(this))).collect(Collectors.joining()) + indentLeft() + indentLeft();
        formatted += machine.getDefsContext().getFunsDefs().isEmpty() ? "" : line() + indentRight() + indentLine("FUNS") + indentRight() + machine.getDefsContext().getFunsDefs().keySet().stream().map(name -> indentLine(machine.getDefsContext().getFunsDefs().get(name).accept(this))).collect(Collectors.joining()) + indentLeft() + indentLeft();
        formatted += line() + indentRight() + indentLine("INVARIANT") + indentRight() + indentLine(machine.getInvariant().accept(this)) + indentLeft() + indentLeft();
        formatted += line() + indentRight() + indentLine("INITIALISATION") + indentRight() + indentLine(machine.getInitialisation().accept(this)) + indentLeft() + indentLeft();
        formatted += line() + indentRight() + indentLine("EVENTS") + line() + indentRight() + machine.getEvents().stream().map(event -> indentLine(event.accept(this))).collect(Collectors.joining()) + indentLeft() + indentLeft();
        return formatted;
    }

    @Override
    public String visit(Event event) {
        return line(event.getName() + " = ") + indentRight() + indentLine(event.getSubstitution().accept(this)) + indentLeft();
    }

    @Override
    public String visit(Skip skip) {
        return "SKIP";
    }

    @Override
    public String visit(Assignments assignments) {
        return assignments.getAssignments().stream().map(assignment -> assignment.accept(this)).collect(Collectors.joining("\n" + indent("")));
    }

    @Override
    public String visit(VarAssignment varAssignment) {
        return varAssignment.getAssignable().accept(this) + " := " + varAssignment.getValue().accept(this);
    }

    @Override
    public String visit(FunAssignment funAssignment) {
        return funAssignment.getAssignable().accept(this) + " := " + funAssignment.getValue().accept(this);
    }

    @Override
    public String visit(Select select) {
        return line("SELECT") + indentRight() + indentLine(select.getCondition().accept(this)) + indentLeft() + indentLine("THEN") + indentRight() + indentLine(select.getSubstitution().accept(this)) + indentLeft() + indent("END");
    }

    @Override
    public String visit(Choice choice) {
        return line("CHOICE") + indentRight() + choice.getSubstitutions().stream().map(substitution -> indentLine(substitution.accept(this))).collect(Collectors.joining(indentLeft() + indentLine("OR") + indentRight())) + indentLeft() + indent("END");
    }

    @Override
    public String visit(Any any) {
        return line("ANY") + indentRight() + any.getQuantifiedVarsDefs().stream().map(varDef -> indentLine(new InDomain(new Var(varDef.getUnPrimedName()), varDef.getDomain()).accept(this))).collect(Collectors.joining()) + indentLeft() + indentLine("WHERE") + indentRight() + indentLine(any.getCondition().accept(this)) + indentLeft() + indentLine("THEN") + indentRight() + indentLine(any.getSubstitution().accept(this)) + indentLeft() + indent("END");
    }

}
