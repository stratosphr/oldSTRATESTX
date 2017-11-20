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
public final class SMTFormatter extends GenericExprFormatter {

    private final DefsContext defsContext;
    private final int foldingLimit;
    private final LinkedHashSet<Fun> funs;
    private boolean isVisitingBoolExpr;
    private LinkedHashSet<AArithExpr> quantifiedVars;

    public SMTFormatter(DefsContext defsContext) {
        this(defsContext, 80);
    }

    @SuppressWarnings("WeakerAccess")
    public SMTFormatter(DefsContext defsContext, int foldingLimit) {
        this.defsContext = defsContext;
        this.foldingLimit = foldingLimit;
        this.funs = new LinkedHashSet<>();
        this.isVisitingBoolExpr = false;
        this.quantifiedVars = new LinkedHashSet<>();
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

    private String formatBoolExpr(String operator, ABoolExpr expr, List<? extends IGenericExprFormattable> operands) {
        boolean wasVisitingBoolExpr = isVisitingBoolExpr;
        if (!isVisitingBoolExpr) {
            isVisitingBoolExpr = true;
        }
        String formatted;
        if (expr instanceof AQuantifier) {
            And funsConstraint = new And(expr.getFuns(defsContext).stream().filter(fun -> ((AQuantifier) expr).getQuantifiedVarsDefs().stream().anyMatch(varDef -> fun.getParameter() instanceof Var && ((Var) fun.getParameter()).getName().equals(varDef.getName()))).map(fun -> new InDomain(fun.getParameter(), defsContext.getFunsDefs().get(fun.getName()).getDomain())).toArray(ABoolExpr[]::new));
            ABoolExpr quantifiedExpr;
            if (expr instanceof ForAll) {
                quantifiedExpr = new Implies(funsConstraint, ((ForAll) expr).getExpr());
            } else if (expr instanceof Exists) {
                quantifiedExpr = new And(funsConstraint, ((AQuantifier) expr).getExpr());
            } else {
                throw new Error("Error: unhandled quantifier type \"" + expr.getClass().getSimpleName() + "\".");
            }
            formatted = line("(" + operator) + indentRight() + indentLine("(" + ((AQuantifier) expr).getQuantifiedVarsDefs().stream().map(varDef -> "(" + varDef.getName() + " Int)").collect(Collectors.joining(" ")) + ")") + indentLine(quantifiedExpr.accept(this)) + indentLeft() + indent(")");
        } else if (operands.isEmpty()) {
            formatted = operator;
        } else {
            formatted = line("(" + operator) + indentRight() + operands.stream().map(operand -> indentLine(operand.accept(this))).collect(Collectors.joining()) + indentLeft() + indent(")");
        }
        if (!wasVisitingBoolExpr) {
            String oldFormatted = formatted;
            formatted = defsContext.getVarsDefs().keySet().stream().map(name -> line(defsContext.getDef(name).accept(this))).collect(Collectors.joining());
            formatted += line();
            formatted += line("(assert " + new And(
                    new And(defsContext.getVarsDefs().keySet().stream().map(name -> new InDomain(new Var(name), defsContext.getDef(name).getDomain())).toArray(ABoolExpr[]::new)),
                    new And(funs.stream().map(fun -> new InDomain(fun.getParameter(), defsContext.getFunsDefs().get(fun.getName()).getDomain())).toArray(ABoolExpr[]::new))
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
        if (!quantifiedVars.contains(fun.getParameter())) {
            funs.add(fun);
        }
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
        return formatBoolExpr("true", aTrue, new ArrayList<>());
    }

    @Override
    public String visit(False aFalse) {
        return formatBoolExpr("false", aFalse, new ArrayList<>());
    }

    @Override
    public String visit(Not not) {
        return fold(formatBoolExpr("not", not, Collections.singletonList(not.getOperand())));
    }

    @Override
    public String visit(Or or) {
        return fold(formatBoolExpr("or", or, or.getOperands()));
    }

    @Override
    public String visit(And and) {
        return fold(formatBoolExpr("and", and, and.getOperands()));
    }

    @Override
    public String visit(Equals equals) {
        return fold(formatBoolExpr("=", equals, equals.getOperands()));
    }

    @Override
    public String visit(LT lt) {
        return fold(formatBoolExpr("<", lt, Arrays.asList(lt.getLeft(), lt.getRight())));
    }

    @Override
    public String visit(LEQ leq) {
        return fold(formatBoolExpr("<=", leq, Arrays.asList(leq.getLeft(), leq.getRight())));
    }

    @Override
    public String visit(GEQ geq) {
        return fold(formatBoolExpr(">=", geq, Arrays.asList(geq.getLeft(), geq.getRight())));
    }

    @Override
    public String visit(GT gt) {
        return fold(formatBoolExpr(">", gt, Arrays.asList(gt.getLeft(), gt.getRight())));
    }

    @Override
    public String visit(InDomain inDomain) {
        return inDomain.getConstraint().accept(this);
    }

    @Override
    public String visit(Implies implies) {
        return formatBoolExpr("=>", implies, Arrays.asList(implies.getCondition(), implies.getThenPart()));
    }

    @Override
    public String visit(ForAll forAll) {
        LinkedHashSet<AArithExpr> oldQuantifiedVars = new LinkedHashSet<>(quantifiedVars);
        quantifiedVars.addAll(forAll.getQuantifiedVarsDefs().stream().map(varDef -> new Var(varDef.getName())).collect(Collectors.toList()));
        String formatted = formatBoolExpr("forall", forAll, new ArrayList<>());
        quantifiedVars = oldQuantifiedVars;
        return formatted;
    }

    @Override
    public String visit(Exists exists) {
        LinkedHashSet<AArithExpr> oldQuantifiedVars = new LinkedHashSet<>(quantifiedVars);
        quantifiedVars.addAll(exists.getQuantifiedVarsDefs().stream().map(varDef -> new Var(varDef.getName())).collect(Collectors.toList()));
        String formatted = formatBoolExpr("exists", exists, new ArrayList<>());
        quantifiedVars = oldQuantifiedVars;
        return formatted;
    }

}
