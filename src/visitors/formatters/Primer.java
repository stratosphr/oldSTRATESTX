package visitors.formatters;

import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.bool.*;
import visitors.formatters.interfaces.IPrimer;

/**
 * Created by gvoiron on 21/11/17.
 * Time : 23:05
 */
public final class Primer implements IPrimer {

    private final static String suffix = "_";
    private final boolean isPriming;
    private boolean isVisitingInvariant;

    public Primer(boolean isPriming) {
        this.isPriming = isPriming;
        this.isVisitingInvariant = false;
    }

    public static String getSuffix() {
        return suffix;
    }

    @Override
    public Int visit(Int anInt) {
        return anInt;
    }

    @Override
    public Const visit(Const aConst) {
        return aConst;
    }

    @Override
    public EnumValue visit(EnumValue enumValue) {
        return enumValue;
    }

    @Override
    public Var visit(Var var) {
        return new Var(var.getUnPrimedName(), isPriming);
    }

    @Override
    public FunVar visit(FunVar funVar) {
        return new FunVar(funVar.getFunName(), funVar.getParameter(), isPriming);
    }

    @Override
    public Fun visit(Fun fun) {
        return new Fun(fun.getUnPrimedName(), isVisitingInvariant ? fun.getParameter().prime() : fun.getParameter(), isPriming);
    }

    @Override
    public Plus visit(Plus plus) {
        return new Plus(plus.getOperands().stream().map(operand -> operand.accept(this)).toArray(AArithExpr[]::new));
    }

    @Override
    public Minus visit(Minus minus) {
        return new Minus(minus.getOperands().stream().map(operand -> operand.accept(this)).toArray(AArithExpr[]::new));
    }

    @Override
    public Times visit(Times times) {
        return new Times(times.getOperands().stream().map(operand -> operand.accept(this)).toArray(AArithExpr[]::new));
    }

    @Override
    public Div visit(Div div) {
        return new Div(div.getOperands().stream().map(operand -> operand.accept(this)).toArray(AArithExpr[]::new));
    }

    @Override
    public Mod visit(Mod mod) {
        return new Mod(mod.getLeft().accept(this), mod.getRight().accept(this));
    }

    @Override
    public False visit(False aFalse) {
        return new False();
    }

    @Override
    public True visit(True aTrue) {
        return new True();
    }

    @Override
    public Not visit(Not not) {
        return new Not(not.getOperand().accept(this));
    }

    @Override
    public And visit(And and) {
        return new And(and.getOperands().stream().map(operand -> operand.accept(this)).toArray(ABoolExpr[]::new));
    }

    @Override
    public Or visit(Or or) {
        return new Or(or.getOperands().stream().map(operand -> operand.accept(this)).toArray(ABoolExpr[]::new));
    }

    @Override
    public Equals visit(Equals equals) {
        return new Equals(equals.getOperands().stream().map(operand -> operand.accept(this)).toArray(AArithExpr[]::new));
    }

    @Override
    public NotEquals visit(NotEquals notEquals) {
        return new NotEquals(notEquals.getLeft().accept(this), notEquals.getRight().accept(this));
    }

    @Override
    public LT visit(LT lt) {
        return new LT(lt.getLeft().accept(this), lt.getRight().accept(this));
    }

    @Override
    public LEQ visit(LEQ leq) {
        return new LEQ(leq.getLeft().accept(this), leq.getRight().accept(this));
    }

    @Override
    public GEQ visit(GEQ geq) {
        return new GEQ(geq.getLeft().accept(this), geq.getRight().accept(this));
    }

    @Override
    public GT visit(GT gt) {
        return new GT(gt.getLeft().accept(this), gt.getRight().accept(this));
    }

    @Override
    public Implies visit(Implies implies) {
        return new Implies(implies.getCondition().accept(this), implies.getThenPart().accept(this));
    }

    @Override
    public ArithITE visit(ArithITE arithITE) {
        return new ArithITE(arithITE.getCondition().accept(this), arithITE.getThenPart().accept(this), arithITE.getElsePart().accept(this));
    }

    @Override
    public InDomain visit(InDomain inDomain) {
        return new InDomain(inDomain.getExpr().accept(this), inDomain.getDomain());
    }

    // TODO: FIX MIGHT BE NEEDED IF QUANTIFIED VARS ARE PRIMED
    @Override
    public ForAll visit(ForAll forAll) {
        return new ForAll(forAll.getExpr().accept(this), forAll.getQuantifiedVarsDefs().toArray(new VarDef[0]));
    }

    @Override
    public Exists visit(Exists exists) {
        return new Exists(exists.getExpr().accept(this), exists.getQuantifiedVarsDefs().toArray(new VarDef[0]));
    }

    @Override
    public Invariant visit(Invariant invariant) {
        isVisitingInvariant = true;
        Invariant primedInvariant = new Invariant(invariant.getExpr().accept(this));
        isVisitingInvariant = false;
        return primedInvariant;
    }

}
