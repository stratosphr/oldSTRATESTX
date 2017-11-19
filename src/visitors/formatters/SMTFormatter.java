package visitors.formatters;

import lang.maths.defs.DefsContext;
import lang.maths.defs.FunDef;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.bool.*;
import visitors.formatters.interfaces.IGenericExprFormattable;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 01:53
 */
public final class SMTFormatter extends IGenericExprFormatter {

    private final DefsContext defsContext;
    private final int foldingLimit;
    private final LinkedHashSet<Fun> funs;
    private boolean isVisitingBoolExpr;

    public SMTFormatter(DefsContext defsContext) {
        this(defsContext, 80);
    }

    private SMTFormatter(DefsContext defsContext, int foldingLimit) {
        this.defsContext = defsContext;
        this.foldingLimit = foldingLimit;
        this.funs = new LinkedHashSet<>();
        this.isVisitingBoolExpr = false;
    }

    private String fold(String formatted) {
        if (formatted.replaceAll("\t", "").length() <= foldingLimit) {
            formatted = Arrays.stream(formatted.replaceAll("\t", "").split("\n")).collect(Collectors.joining(" ")).replaceAll(" [)]", ")");
        }
        return formatted;
    }

    private String formatArithExpr(String formatted) {
        return formatted;
    }

    private String formatBoolExpr(String operator, List<? extends IGenericExprFormattable> operands) {
        boolean wasVisitingBoolExpr = isVisitingBoolExpr;
        if (!isVisitingBoolExpr) {
            isVisitingBoolExpr = true;
        }
        String formatted = operands.isEmpty() ? operator : line("(" + operator) + indentRight() + operands.stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")");
        if (!wasVisitingBoolExpr) {
            String oldFormatted = formatted;
            formatted = defsContext.getVarsDefs().keySet().stream().map(name -> line(defsContext.getDef(name).accept(this))).collect(Collectors.joining());
            formatted += line();
            formatted += line("(assert " + new And(
                    new And(defsContext.getVarsDefs().keySet().stream().map(name -> new AInDomain(new Var(name), defsContext.getDef(name).getDomain())).toArray(ABoolExpr[]::new)),
                    new And(funs.stream().map(fun -> new AInDomain(fun.getParameter(), defsContext.getFunsDefs().get(fun.getName()).getDomain())).toArray(ABoolExpr[]::new))
            ).accept(this) + ")");
            formatted += line();
            formatted += defsContext.getFunsDefs().keySet().stream().map(name -> line(defsContext.getDef(name).accept(this))).collect(Collectors.joining());
            formatted += line();
            formatted += "(assert " + oldFormatted + ")";
        }
        return formatted;
    }

    @Override
    public String visit(VarDef varDef) {
        return "(declare-fun " + varDef.getName() + " () Int)";
    }

    @Override
    public String visit(FunDef funDef) {
        Var index = new Var("i!");
        String formatted = line("(define-fun " + funDef.getName() + " ((" + index + " Int)) Int") + indentRight();
        List<AValue> domainElements = new ArrayList<>(funDef.getDomain().getElements());
        ListIterator<AValue> iterator = domainElements.listIterator(domainElements.size());
        AValue firstDomainElement = iterator.previous();
        ArithITE arithITE = new ArithITE(new Equals(index, firstDomainElement), new Var(funDef.getName() + "!" + firstDomainElement), new Int(0));
        while (iterator.hasPrevious()) {
            AValue element = iterator.previous();
            arithITE = new ArithITE(new Equals(index, element), new Var(funDef.getName() + "!" + element), arithITE);
        }
        formatted += indentLine(arithITE.accept(this));
        formatted += indentLeft() + ")";
        return formatted;
    }

    @Override
    public String visit(Const aConst) {
        return aConst.getName();
    }

    @Override
    public String visit(Int anInt) {
        return formatArithExpr(anInt.getValue().toString());
    }

    @Override
    public String visit(Var var) {
        return formatArithExpr(var.getName());
    }

    @Override
    public String visit(Fun fun) {
        funs.add(fun);
        return fold(formatArithExpr("(" + fun.getName() + " " + fun.getParameter().accept(this) + ")"));
    }

    @Override
    public String visit(Plus plus) {
        return fold(formatArithExpr(line("(+") + indentRight() + plus.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")")));
    }

    @Override
    public String visit(Minus minus) {
        return fold(formatArithExpr(line("(-") + indentRight() + minus.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")")));
    }

    @Override
    public String visit(Times times) {
        return fold(formatArithExpr(line("(*") + indentRight() + times.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")")));
    }

    @Override
    public String visit(Div div) {
        return fold(formatArithExpr(line("(/") + indentRight() + div.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")")));
    }

    @Override
    public String visit(Mod mod) {
        return fold(formatArithExpr(line("(mod") + indentRight() + mod.getOperands().stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")")));
    }

    @Override
    public String visit(ArithITE arithITE) {
        return formatArithExpr(line("(ite") + indentRight() + indentLine(arithITE.getCondition().accept(this)) + indentLine(arithITE.getThenPart().accept(this)) + indentLine(arithITE.getElsePart().accept(this)) + indentLeft() + indent(")"));
    }

    @Override
    public String visit(True aTrue) {
        return formatBoolExpr("true", new ArrayList<>());
    }

    @Override
    public String visit(False aFalse) {
        return formatBoolExpr("false", new ArrayList<>());
    }

    @Override
    public String visit(Not not) {
        return fold(formatBoolExpr("not", Collections.singletonList(not.getOperand())));
    }

    @Override
    public String visit(Or or) {
        return fold(formatBoolExpr("or", or.getOperands()));
    }

    @Override
    public String visit(And and) {
        return fold(formatBoolExpr("and", and.getOperands()));
    }

    @Override
    public String visit(Equals equals) {
        return fold(formatBoolExpr("=", equals.getOperands()));
    }

    @Override
    public String visit(LT lt) {
        return fold(formatBoolExpr("<", Arrays.asList(lt.getLeft(), lt.getRight())));
    }

    @Override
    public String visit(LEQ leq) {
        return fold(formatBoolExpr("<=", Arrays.asList(leq.getLeft(), leq.getRight())));
    }

    @Override
    public String visit(GEQ geq) {
        return fold(formatBoolExpr(">=", Arrays.asList(geq.getLeft(), geq.getRight())));
    }

    @Override
    public String visit(GT gt) {
        return fold(formatBoolExpr(">", Arrays.asList(gt.getLeft(), gt.getRight())));
    }

    @Override
    public String visit(AInDomain aInDomain) {
        return aInDomain.getConstraint().accept(this);
    }

}
