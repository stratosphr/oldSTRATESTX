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
public class SMTFormatter2 extends AFormatter implements ISMTFormatter {

    private final DefsContext defsContext;
    private final int foldingLimit;
    private boolean isVisitingBoolExpr;

    public SMTFormatter2(DefsContext defsContext) {
        this(defsContext, 0);
    }

    public SMTFormatter2(DefsContext defsContext, int foldingLimit) {
        this.defsContext = defsContext;
        this.foldingLimit = foldingLimit;
        this.isVisitingBoolExpr = false;
    }

    public String format(ABoolExpr expr) {
        String formatted = defsContext.getConstsDefs().keySet().stream().map(name -> line("(define-fun " + name + " () Int " + defsContext.getConstsDefs().get(name) + ")")).collect(Collectors.joining());
        formatted += defsContext.getVarsDefs().values().stream().map(varDef -> line(varDef.accept(this))).collect(Collectors.joining());
        formatted += "(assert " + expr.accept(this) + ")";
        System.err.println(formatted);
        System.err.println("###############################################");
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
    public String visit(FunDef funDef) {
        System.exit(42);
        return null;
    }

    @Override
    public String visit(VarDef varDef) {
        return "(declare-fun " + varDef.getUnPrimedName() + " () Int)";
    }

    @Override
    public String visit(FunVarDef funVarDef) {
        return "(declare-fun " + funVarDef.getUnPrimedName() + " () Int)";
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
    public String visit(EnumValue enumValue) {
        System.exit(46);
        return null;
    }

    @Override
    public String visit(Var var) {
        return var.getRealName();
    }

    @Override
    public String visit(FunVar funVar) {
        System.exit(48);
        return null;
    }

    @Override
    public String visit(Fun fun) {
        System.exit(49);
        return null;
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
        System.exit(55);
        return null;
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
        System.exit(59);
        return null;
    }

    @Override
    public String visit(And and) {
        return fold(line("(and") + indentRight() + and.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft()) + indent(")");
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
        System.exit(67);
        return null;
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
        System.exit(71);
        return null;
    }

}
