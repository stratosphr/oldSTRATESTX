package visitors.formatters;

import lang.maths.defs.DefsContext;
import lang.maths.defs.FunDef;
import lang.maths.defs.FunVarDef;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.bool.*;
import visitors.formatters.interfaces.ISMTFormatter;

import java.util.Arrays;
import java.util.stream.Collectors;

/**
 * Created by gvoiron on 22/11/17.
 * Time : 20:34
 */
public class SMTFormatter extends AFormatter implements ISMTFormatter {

    private final DefsContext defsContext;
    private final int foldingLimit;

    public SMTFormatter(DefsContext defsContext) {
        this(defsContext, 80);
    }

    public SMTFormatter(DefsContext defsContext, int foldingLimit) {
        this.defsContext = defsContext;
        this.foldingLimit = foldingLimit;
    }

    public String format(ABoolExpr expr) {
        String formatted = "";
        formatted += defsContext.getConstsDefs().keySet().stream().map(name -> line("(define-fun " + name + " () Int " + defsContext.getConstsDefs().get(name) + ")")).collect(Collectors.joining());
        formatted += defsContext.getVarsDefs().values().stream().map(varDef -> line(varDef.accept(this))).collect(Collectors.joining());
        formatted += defsContext.getVarsDefs().values().stream().map(varDef -> line(new VarDef<>(varDef.getVar().accept(new Primer(true)), varDef.getDomain()).accept(this))).collect(Collectors.joining());
        formatted += defsContext.getFunVarsDefs().values().stream().map(funVarDef -> line(funVarDef.accept(this))).collect(Collectors.joining());
        formatted += defsContext.getFunVarsDefs().values().stream().map(funVarDef -> line(new FunVarDef<>(funVarDef.getVar().accept(new Primer(true)), funVarDef.getDomain()).accept(this))).collect(Collectors.joining());
        formatted += defsContext.getFunsDefs().values().stream().map(funDef -> line(funDef.accept(this))).collect(Collectors.joining());
        formatted += defsContext.getFunsDefs().values().stream().map(funDef -> line(new FunDef(new Var(funDef.getName()).accept(new Primer(true)).getName(), funDef.getDomain(), funDef.getCoDomain()).accept(this))).collect(Collectors.joining());
        formatted += "(assert " + expr.accept(this) + ")";
        return formatted;
    }

    private String fold(String formatted) {
        String tabsReplaced = formatted.replaceAll("\t", "");
        if (tabsReplaced.length() <= foldingLimit) {
            formatted = Arrays.stream(tabsReplaced.split("\n")).collect(Collectors.joining(" ")).replaceAll(" [)]", ")");
        }
        return formatted;
    }

    @Override
    public String visit(VarDef varDef) {
        return "(declare-fun " + varDef.getVar().accept(this) + " () Int)";
    }

    @Override
    public String visit(FunVarDef funVarDef) {
        return "(declare-fun " + funVarDef.getVar().accept(this) + " () Int)";
    }

    @Override
    public String visit(FunDef funDef) {
        Var index = new Var("i!");
        String formatted = line("(define-fun " + funDef.getName() + " ((" + index.accept(this) + " Int)) Int");
        formatted += indentRight() + indentLine(funDef.getDomain().getElements().descendingSet().stream().filter(o -> !o.equals(funDef.getDomain().getElements().last())).reduce(new ArithITE(new Equals(index, funDef.getDomain().getElements().last()), new FunVar(new Fun(funDef.getName(), funDef.getDomain().getElements().last())), funDef.getDomain().getElements().first()), (element1, o2) -> new ArithITE(new Equals(index, o2), new FunVar(new Fun(funDef.getName(), o2)), element1), (arithITE1, arithITE2) -> arithITE1).accept(this)) + indentLeft();
        formatted += indent(")");
        return formatted;
    }

    @Override
    public String visit(Const aConst) {
        return fold(aConst.getName());
    }

    @Override
    public String visit(Int anInt) {
        return fold(anInt.getValue().toString());
    }

    @Override
    public String visit(EnumValue enumValue) {
        return fold(new Int(enumValue.getValue()).accept(this));
    }

    @Override
    public String visit(Var var) {
        return fold(var.getName());
    }

    @Override
    public String visit(FunVar funVar) {
        return fold(funVar.getName());
    }

    @Override
    public String visit(Fun fun) {
        return fold("(" + fun.getName() + " " + fun.getParameter().accept(this) + ")");
    }

    @Override
    public String visit(Plus plus) {
        System.exit(50);
        return null;
    }

    @Override
    public String visit(Minus minus) {
        System.exit(51);
        return null;
    }

    @Override
    public String visit(Times times) {
        System.exit(52);
        return null;
    }

    @Override
    public String visit(Div div) {
        System.exit(53);
        return null;
    }

    @Override
    public String visit(Mod mod) {
        System.exit(54);
        return null;
    }

    @Override
    public String visit(ArithITE arithITE) {
        return line("(ite") + indentRight() + indentLine(arithITE.getCondition().accept(this)) + indentLine(arithITE.getThenPart().accept(this)) + indentLine(arithITE.getElsePart().accept(this)) + indentLeft() + indent(")");
    }

    @Override
    public String visit(True aTrue) {
        System.exit(56);
        return null;
    }

    @Override
    public String visit(False aFalse) {
        System.exit(57);
        return null;
    }

    @Override
    public String visit(Not not) {
        System.exit(58);
        return null;
    }

    @Override
    public String visit(Or or) {
        return fold(or.getOperands().isEmpty() ? new False().accept(this) : line("(or") + indentRight() + or.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")"));
    }

    @Override
    public String visit(And and) {
        return fold(and.getOperands().isEmpty() ? new True().accept(this) : line("(and") + indentRight() + and.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")"));
    }

    @Override
    public String visit(Equals equals) {
        return fold(line("(=") + indentRight() + equals.getOperands().stream().map(expr -> indentLine(expr.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")"));
    }

    @Override
    public String visit(NotEquals notEquals) {
        System.exit(62);
        return null;
    }

    @Override
    public String visit(LT lt) {
        System.exit(63);
        return null;
    }

    @Override
    public String visit(LEQ leq) {
        System.exit(64);
        return null;
    }

    @Override
    public String visit(GEQ geq) {
        System.exit(65);
        return null;
    }

    @Override
    public String visit(GT gt) {
        System.exit(66);
        return null;
    }

    @Override
    public String visit(InDomain inDomain) {
        return fold(inDomain.getConstraint().accept(this));
    }

    @Override
    public String visit(Implies implies) {
        System.exit(68);
        return null;
    }

    @Override
    public String visit(ForAll forAll) {
        System.exit(69);
        return null;
    }

    @Override
    public String visit(Exists exists) {
        System.exit(70);
        return null;
    }

    @Override
    public String visit(Invariant invariant) {
        return fold(invariant.getExpr().accept(this));
    }

}
