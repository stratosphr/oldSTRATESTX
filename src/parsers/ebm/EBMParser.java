package parsers.ebm;

import lang.eventb.Event;
import lang.eventb.Machine;
import lang.eventb.substitutions.*;
import lang.maths.defs.DefsContext;
import lang.maths.defs.FunDef;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.bool.*;
import lang.maths.exprs.set.*;
import lang.maths.exprs.set.Enum;
import parsers.xml.XMLNode;
import parsers.xml.XMLParser;
import solvers.z3.Z3;
import solvers.z3.Z3Result;
import utilities.ResourcesManager;
import utilities.Tuple;

import java.io.File;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

import static utilities.ResourcesManager.EXMLSchema.EBM;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 16:06
 */
public final class EBMParser {

    private final DefsContext defsContext;

    // TODO : ERROR MANAGEMENT COULD BE BETTER IF WE KEPT A LIST OF ERRORS AND THEN THROW AN ERROR AT THE VERY END OF THE PARSING PROCESS IF THERE WERE ANY
    // TODO : ADD MISSING ELEMENTS TO SCHEMA AND MAKE SURE EVERYTHING IS COHERENT WITH THE PARSER
    public EBMParser() {
        this.defsContext = new DefsContext();
    }

    public Machine parse(File file) {
        XMLParser xmlParser = new XMLParser(true);
        XMLNode root = xmlParser.parse(file, ResourcesManager.getXMLSchema(EBM));
        try {
            root.assertConformsTo("model", 3, 7, "sets-defs", "consts-defs", "vars-defs", "funs-defs", "invariant", "initialisation", "events");
            XMLNode constsDefsNode = root.getFirstChildWithName("consts-defs");
            XMLNode setsDefsNode = root.getFirstChildWithName("sets-defs");
            XMLNode varsDefsNode = root.getFirstChildWithName("vars-defs");
            XMLNode funsDefsNode = root.getFirstChildWithName("funs-defs");
            XMLNode invariantNode = root.getFirstChildWithName("invariant");
            XMLNode initialisationNode = root.getFirstChildWithName("initialisation");
            XMLNode eventsNode = root.getFirstChildWithName("events");
            LinkedHashMap<String, AArithExpr> constsDefs = parseConstsDefs(constsDefsNode);
            LinkedHashMap<String, ASetExpr> setsDefs = parseSetsDefs(setsDefsNode);
            LinkedHashSet<VarDef> varsDefs = parseVarsDefs(varsDefsNode);
            varsDefs.forEach(defsContext::addDef);
            LinkedHashSet<FunDef> funsDefs = parseFunsDefs(funsDefsNode);
            funsDefs.forEach(defsContext::addDef);
            ABoolExpr invariant = parseInvariant(invariantNode);
            ASubstitution initialisation = parseInitialisation(initialisationNode);
            LinkedHashSet<Event> events = parseEvents(eventsNode);
            return new Machine(root.getAttributes().get("name"), constsDefs, setsDefs, defsContext, invariant, initialisation, events);
        } catch (Error e) {
            e.printStackTrace();
            throw new Error(e.fillInStackTrace());
        }
    }

    private LinkedHashMap<String, AArithExpr> parseConstsDefs(XMLNode node) {
        LinkedHashMap<String, AArithExpr> constsDefs = new LinkedHashMap<>();
        if (node != null) {
            node.assertConformsTo("consts-defs", 1, -1, "const-def");
            node.getChildren().stream().map(this::parseConstDef).forEach(tuple -> constsDefs.put(tuple.getLeft(), tuple.getRight()));
        }
        return constsDefs;
    }

    // TODO: MAKING parseConst() RETURN A Var COULD AVOID THE NECESSITY OF USING THE RIGHT ORDER WHEN DEFINING CONSTS DEPENDING ON OTHER CONSTS
    private Tuple<String, AArithExpr> parseConstDef(XMLNode node) {
        node.assertConformsTo("const-def", 1, 1, "int", "const", "plus", "minus", "times", "div", "mod");
        AArithExpr expr = parseArithExpr(node.getChildren().get(0));
        DefsContext tmpDefsContext = new DefsContext();
        if (!expr.getFuns().isEmpty() || !expr.getVars(tmpDefsContext).isEmpty()) {
            throw new Error("Error l." + node.getChildren().get(0).getLine() + ",c." + node.getColumn() + ": the value of a const (here \"" + node.getAttributes().get("name") + "\") cannot depend on any variable or function.");
        }
        Var valueVar = new Var("value!");
        defsContext.getConstsDefs().forEach(tmpDefsContext::addConstDef);
        tmpDefsContext.addFreshVar(valueVar);
        Z3Result result = Z3.checkSAT(new Equals(valueVar, expr), tmpDefsContext);
        if (result.isSAT()) {
            defsContext.addConstDef(node.getAttributes().get("name"), new Int(result.getModel().get(valueVar).getValue()));
            return new Tuple<>(node.getAttributes().get("name"), expr);
        } else {
            throw new Error("Error l." + node.getChildren().get(0).getLine() + ",c." + node.getColumn() + ": unable to compute the value of const \"" + node.getAttributes().get("name") + "\" with expression \"" + expr + "\".");
        }
    }

    private LinkedHashMap<String, ASetExpr> parseSetsDefs(XMLNode node) {
        LinkedHashMap<String, ASetExpr> setsDefs = new LinkedHashMap<>();
        if (node != null) {
            node.assertConformsTo("sets-defs", 1, -1, "set-def");
            node.getChildren().stream().map(this::parseSetDef).forEach(tuple -> setsDefs.put(tuple.getLeft(), tuple.getRight()));
        }
        return setsDefs;
    }

    private Tuple<String, ASetExpr> parseSetDef(XMLNode node) {
        node.assertConformsTo("set-def", 1, 1, "usual", "named-set", "set", "enum", "range");
        return new Tuple<>(node.getAttributes().get("name"), parseSetExpr(node.getChildren().get(0)));
    }

    private LinkedHashSet<VarDef> parseVarsDefs(XMLNode node) {
        LinkedHashSet<VarDef> varsDefs = new LinkedHashSet<>();
        if (node != null) {
            node.assertConformsTo("vars-defs", 1, -1, "var-def");
            node.getChildren().stream().map(this::parseVarDef).forEach(varsDefs::add);
        }
        return varsDefs;
    }

    private VarDef parseVarDef(XMLNode node) {
        node.assertConformsTo("var-def", 1, 1, "named-set", "set", "enum", "range", "usual");
        ASetExpr domain = parseSetExpr(node.getChildren().get(0));
        if (domain.isEmpty(defsContext)) {
            throw new Error("Error l." + node.getLine() + ",c." + node.getColumn() + ": the domain of a variable (here \"" + node.getAttributes().get("name") + "\") cannot be empty (here " + domain + ").");
        }
        return new VarDef<>(new Var(node.getAttributes().get("name")), domain);
    }

    private LinkedHashSet<FunDef> parseFunsDefs(XMLNode node) {
        LinkedHashSet<FunDef> funsDefs = new LinkedHashSet<>();
        if (node != null) {
            node.assertConformsTo("funs-defs", 1, -1, "fun-def");
            node.getChildren().stream().map(this::parseFunDef).forEach(funsDefs::add);
        }
        return funsDefs;
    }

    private FunDef parseFunDef(XMLNode node) {
        node.assertConformsTo("fun-def", 2, 2, "named-set", "set", "enum", "range", "usual");
        if (node.getChildren().get(0).getName().equals("usual")) {
            throw new Error("Error l." + node.getLine() + ",c." + node.getColumn() + ": The domain of a function (here \"" + node.getAttributes().get("name") + "\") cannot be an infinite set (here " + node.getChildren().get(0).getAttributes().get("name") + ").");
        }
        AFiniteSetExpr domain = parseFiniteSetExpr(node.getChildren().get(0));
        ASetExpr coDomain = parseSetExpr(node.getChildren().get(1));
        if (domain.isEmpty(defsContext)) {
            throw new Error("Error l." + node.getLine() + ",c." + node.getColumn() + ": The domain of a variable (here \"" + node.getAttributes().get("name") + "\") cannot be empty (here " + domain + ").");
        }
        return new FunDef(node.getAttributes().get("name"), domain, coDomain);
    }

    private ABoolExpr parseInvariant(XMLNode node) {
        if (node != null) {
            node.assertConformsTo("invariant", 1, 1, "false", "true", "not", "and", "or", "equals", "neq", "lt", "leq", "geq", "gt", "in-domain", "implies", "forall", "exists");
            return new Invariant(parseBoolExpr(node.getChildren().get(0)));
        }
        return new True();
    }

    // TODO: WARNING SHOULD BE THROWN
    // TODO: CHECK THAT NO Var OR Fun IS USED IN INITIALISATION EXCEPT AS FIRST CHILD OF Assignment
    private ASubstitution parseInitialisation(XMLNode node) {
        if (node != null) {
            node.assertConformsTo("initialisation", 1, 1, "skip", "var-assignment", "fun-assignment", "assignments", "select", "choice", "any");
            return parseSubstitution(node.getChildren().get(0));
        }
        System.err.println("Warning: No initialisation found. Initial values of assignables will be random values taken from their respective domains of definition.");
        return new Skip();
    }

    private LinkedHashSet<Event> parseEvents(XMLNode node) {
        LinkedHashSet<Event> events = new LinkedHashSet<>();
        if (node != null) {
            node.assertConformsTo("events", 1, -1, "event");
            node.getChildren().stream().map(this::parseEvent).forEach(events::add);
        }
        return events;
    }

    private AArithExpr parseArithExpr(XMLNode node) {
        switch (node.getName()) {
            case "int":
                return parseInt(node);
            case "const":
                return parseConst(node);
            case "enum-value":
                return parseEnumValue(node);
            case "var":
                return parseVar(node);
            case "fun":
                return parseFun(node);
            case "plus":
                return parsePlus(node);
            case "minus":
                return parseMinus(node);
            case "times":
                return parseTimes(node);
            case "div":
                return parseDiv(node);
            case "mod":
                return parseMod(node);
            default:
                throw new Error("Error l." + node.getLine() + ",c." + node.getColumn() + ": unable to parse the following unknown arithmetic expression:\n" + node);
        }
    }

    private Int parseInt(XMLNode node) {
        node.assertConformsTo("int", 0, 0);
        return new Int(Integer.parseInt(node.getAttributes().get("value")));
    }

    private Const parseConst(XMLNode node) {
        node.assertConformsTo("const", 0, 0);
        if (!defsContext.getConstsDefs().containsKey(node.getAttributes().get("name"))) {
            throw new Error("Error l." + node.getLine() + ",c." + node.getColumn() + ": undefined constant \"" + node.getAttributes().get("name") + "\".");
        }
        return new Const(node.getAttributes().get("name"), defsContext.getConstsDefs().get(node.getAttributes().get("name")).getValue());
    }

    private EnumValue parseEnumValue(XMLNode node) {
        node.assertConformsTo("enum-value", 0, 0);
        return new EnumValue(node.getAttributes().get("name"));
    }

    private Var parseVar(XMLNode node) {
        node.assertConformsTo("var", 0, 0);
        return new Var(node.getAttributes().get("name"));
    }

    private Fun parseFun(XMLNode node) {
        node.assertConformsTo("fun", 1, 1, "int", "const", "enum-value", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new Fun(node.getAttributes().get("name"), parseArithExpr(node.getChildren().get(0)));
    }

    private Plus parsePlus(XMLNode node) {
        node.assertConformsTo("plus", 2, -1, "int", "const", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new Plus(node.getChildren().stream().map(this::parseArithExpr).toArray(AArithExpr[]::new));
    }

    private Minus parseMinus(XMLNode node) {
        node.assertConformsTo("minus", 2, -1, "int", "const", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new Minus(node.getChildren().stream().map(this::parseArithExpr).toArray(AArithExpr[]::new));
    }

    private Times parseTimes(XMLNode node) {
        node.assertConformsTo("times", 2, -1, "int", "const", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new Times(node.getChildren().stream().map(this::parseArithExpr).toArray(AArithExpr[]::new));
    }

    private Div parseDiv(XMLNode node) {
        node.assertConformsTo("div", 2, -1, "int", "const", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new Div(node.getChildren().stream().map(this::parseArithExpr).toArray(AArithExpr[]::new));
    }

    private AArithExpr parseMod(XMLNode node) {
        node.assertConformsTo("mod", 2, 2, "int", "const", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new Mod(parseArithExpr(node.getChildren().get(0)), parseArithExpr(node.getChildren().get(1)));
    }

    private ABoolExpr parseBoolExpr(XMLNode node) {
        switch (node.getName()) {
            case "false":
                return parseFalse(node);
            case "true":
                return parseTrue(node);
            case "not":
                return parseNot(node);
            case "and":
                return parseAnd(node);
            case "or":
                return parseOr(node);
            case "equals":
                return parseEquals(node);
            case "neq":
                return parseNotEquals(node);
            case "lt":
                return parseLT(node);
            case "leq":
                return parseLEQ(node);
            case "geq":
                return parseGEQ(node);
            case "gt":
                return parseGT(node);
            case "in-domain":
                return parseInDomain(node);
            case "implies":
                return parseImplies(node);
            case "forall":
                return parseForAll(node);
            case "exists":
                return parseExists(node);
            default:
                throw new Error("Error l." + node.getLine() + ",c." + node.getColumn() + ": unable to parse the following unknown boolean expression:\n" + node);
        }
    }

    private False parseFalse(XMLNode node) {
        node.assertConformsTo("false", 0, 0);
        return new False();
    }

    private True parseTrue(XMLNode node) {
        node.assertConformsTo("true", 0, 0);
        return new True();
    }

    private Not parseNot(XMLNode node) {
        node.assertConformsTo("not", 1, 1, "false", "true", "not", "and", "or", "equals", "neq", "lt", "leq", "geq", "gt", "in-domain", "implies", "forall", "exists");
        return new Not(parseBoolExpr(node.getChildren().get(0)));
    }

    private And parseAnd(XMLNode node) {
        node.assertConformsTo("and", 2, -1, "false", "true", "not", "and", "or", "equals", "neq", "lt", "leq", "geq", "gt", "in-domain", "implies", "forall", "exists");
        return new And(node.getChildren().stream().map(this::parseBoolExpr).toArray(ABoolExpr[]::new));
    }

    private Or parseOr(XMLNode node) {
        node.assertConformsTo("or", 2, -1, "false", "true", "not", "and", "or", "equals", "neq", "lt", "leq", "geq", "gt", "in-domain", "implies", "forall", "exists");
        return new Or(node.getChildren().stream().map(this::parseBoolExpr).toArray(ABoolExpr[]::new));
    }

    // TODO: CHECK IF WE COMPARE EnumValue ELEMENTS WITH EnumValue ELEMENTS OR Var OR Fun WHOSE DOMAIN (RESP. CODOMAIN) ARE A SET CONTAINING EnumValue ELEMENTS ONLY OTHERWISE x = aEnumValue MIGHT ANSWER TRUE EVEN IF x IS AN INT OR A CONST
    private Equals parseEquals(XMLNode node) {
        node.assertConformsTo("equals", 2, -1, "int", "const", "enum-value", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new Equals(node.getChildren().stream().map(this::parseArithExpr).toArray(AArithExpr[]::new));
    }

    private NotEquals parseNotEquals(XMLNode node) {
        node.assertConformsTo("neq", 2, 2, "int", "const", "enum-value", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new NotEquals(parseArithExpr(node.getChildren().get(0)), parseArithExpr(node.getChildren().get(1)));
    }

    private LT parseLT(XMLNode node) {
        node.assertConformsTo("lt", 2, 2, "int", "const", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new LT(parseArithExpr(node.getChildren().get(0)), parseArithExpr(node.getChildren().get(1)));
    }

    private LEQ parseLEQ(XMLNode node) {
        node.assertConformsTo("leq", 2, 2, "int", "const", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new LEQ(parseArithExpr(node.getChildren().get(0)), parseArithExpr(node.getChildren().get(1)));
    }

    private GEQ parseGEQ(XMLNode node) {
        node.assertConformsTo("geq", 2, 2, "int", "const", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new GEQ(parseArithExpr(node.getChildren().get(0)), parseArithExpr(node.getChildren().get(1)));
    }

    private GT parseGT(XMLNode node) {
        node.assertConformsTo("gt", 2, 2, "int", "const", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new GT(parseArithExpr(node.getChildren().get(0)), parseArithExpr(node.getChildren().get(1)));
    }

    private InDomain parseInDomain(XMLNode node) {
        node.assertConformsTo("in-domain", 2, 2, "int", "const", "enum-value", "var", "fun", "plus", "minus", "times", "div", "mod", "usual", "named-set", "set", "enum", "range");
        return new InDomain(parseArithExpr(node.getChildren().get(0)), parseSetExpr(node.getChildren().get(1)));
    }

    private Implies parseImplies(XMLNode node) {
        node.assertConformsTo("implies", 2, 2, "false", "true", "not", "and", "or", "equals", "neq", "lt", "leq", "geq", "gt", "in-domain", "implies", "forall", "exists");
        return new Implies(parseBoolExpr(node.getChildren().get(0)), parseBoolExpr(node.getChildren().get(1)));
    }

    private ForAll parseForAll(XMLNode node) {
        node.assertConformsTo("forall", 2, 2, "vars-defs", "false", "true", "not", "and", "or", "equals", "neq", "lt", "leq", "geq", "gt", "in-domain", "implies", "forall", "exists");
        return new ForAll(parseBoolExpr(node.getChildren().get(0)), parseVarsDefs(node.getChildren().get(1)).toArray(new VarDef[0]));
    }

    private Exists parseExists(XMLNode node) {
        node.assertConformsTo("exists", 2, 2, "vars-defs", "false", "true", "not", "and", "or", "equals", "neq", "lt", "leq", "geq", "gt", "in-domain", "implies", "forall", "exists");
        return new Exists(parseBoolExpr(node.getChildren().get(0)), parseVarsDefs(node.getChildren().get(1)).toArray(new VarDef[0]));
    }

    private ASetExpr parseSetExpr(XMLNode node) {
        switch (node.getName()) {
            case "usual":
                return parseUsualSet(node);
            default:
                return parseFiniteSetExpr(node);
        }
    }

    private ASetExpr parseUsualSet(XMLNode node) {
        node.assertConformsTo("usual", 0, 0);
        System.err.println("Warning: parsing returns finite set by default for the moment, this must be fixed.");
        return new Set(new Int(0));
    }

    private AFiniteSetExpr parseFiniteSetExpr(XMLNode node) {
        switch (node.getName()) {
            case "named-set":
                return parseNamedSet(node);
            case "set":
                return parseSet(node);
            case "enum":
                return parseEnum(node);
            case "range":
                return parseRange(node);
            default:
                throw new Error("Error l." + node.getLine() + ",c." + node.getColumn() + ": Unable to parse the following unknown set expression:\n" + node);
        }
    }

    private AFiniteSetExpr parseNamedSet(XMLNode node) {
        node.assertConformsTo("named-set", 0, 0);
        return new NamedSet(node.getAttributes().get("name"));
    }

    private Set parseSet(XMLNode node) {
        node.assertConformsTo("set", 0, -1, "int", "const", "plus", "minus", "times", "div", "mod");
        return new Set(node.getChildren().stream().map(this::parseArithExpr).toArray(AArithExpr[]::new));
    }

    private Enum parseEnum(XMLNode node) {
        node.assertConformsTo("enum", 0, -1, "enum-value");
        return new Enum(node.getChildren().stream().map(this::parseEnumValue).toArray(EnumValue[]::new));
    }

    private Range parseRange(XMLNode node) {
        node.assertConformsTo("range", 2, 2, "int", "const", "plus", "minus", "times", "div", "mod");
        return new Range(parseArithExpr(node.getChildren().get(0)), parseArithExpr(node.getChildren().get(1)));
    }

    private ASubstitution parseSubstitution(XMLNode node) {
        switch (node.getName()) {
            case "skip":
                return parseSkip(node);
            case "var-assignment":
            case "fun-assignment":
                return parseAssignment(node);
            case "assignments":
                return parseAssignments(node);
            case "select":
                return parseSelect(node);
            case "choice":
                return parseChoice(node);
            case "any":
                return parseAny(node);
            default:
                throw new Error("Error l." + node.getLine() + ",c." + node.getColumn() + ": unable to parse the following unknown substitution:\n" + node);
        }
    }

    private AAssignment parseAssignment(XMLNode node) {
        switch (node.getName()) {
            case "var-assignment":
                return parseVarAssignment(node);
            case "fun-assignment":
                return parseFunAssignment(node);
            default:
                throw new Error("Error l." + node.getLine() + ",c." + node.getColumn() + ": unable to parse the following unknown assignment substitution:\n" + node);
        }
    }

    private Skip parseSkip(XMLNode node) {
        node.assertConformsTo("skip", 0, 0);
        return new Skip();
    }

    // TODO: CHECK THAT Var IS DEFINED AND IS ASSIGNED TO A VALUE IN ITS DOMAIN
    private VarAssignment parseVarAssignment(XMLNode node) {
        node.assertConformsTo("var-assignment", 2, 2, "var", "int", "const", "enum-value", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new VarAssignment(parseVar(node.getChildren().get(0)), parseArithExpr(node.getChildren().get(1)));
    }

    // TODO: CHECK THAT Fun IS DEFINED AND IS ASSIGNED TO A VALUE IN ITS CODOMAIN
    private FunAssignment parseFunAssignment(XMLNode node) {
        node.assertConformsTo("fun-assignment", 2, 2, "fun", "int", "const", "enum-value", "var", "fun", "plus", "minus", "times", "div", "mod");
        return new FunAssignment(parseFun(node.getChildren().get(0)), parseArithExpr(node.getChildren().get(1)));
    }

    private Assignments parseAssignments(XMLNode node) {
        node.assertConformsTo("assignments", 2, -1, "var-assignment", "fun-assignment");
        return new Assignments(node.getChildren().stream().map(this::parseAssignment).toArray(AAssignment[]::new));
    }

    private Select parseSelect(XMLNode node) {
        node.assertConformsTo("select", 2, 2, "false", "true", "not", "and", "or", "equals", "neq", "lt", "leq", "geq", "gt", "in-domain", "implies", "forall", "exists", "skip", "var-assignment", "fun-assignment", "assignments", "select", "choice", "any");
        return new Select(parseBoolExpr(node.getChildren().get(0)), parseSubstitution(node.getChildren().get(1)));
    }

    private Choice parseChoice(XMLNode node) {
        node.assertConformsTo("choice", 2, -1, "skip", "var-assignment", "fun-assignment", "assignments", "select", "choice", "any");
        return new Choice(node.getChildren().stream().map(this::parseSubstitution).toArray(ASubstitution[]::new));
    }

    private Any parseAny(XMLNode node) {
        node.assertConformsTo("any", 2, -1, "vars-defs", "false", "true", "not", "and", "or", "equals", "neq", "lt", "leq", "geq", "gt", "in-domain", "implies", "forall", "exists", "skip", "var-assignment", "fun-assignment", "assignments", "select", "choice", "any");
        return new Any(parseBoolExpr(node.getChildren().get(1)), parseSubstitution(node.getChildren().get(2)), parseVarsDefs(node.getChildren().get(0)).toArray(new VarDef[0]));
    }

    private Event parseEvent(XMLNode node) {
        node.assertConformsTo("event", 1, 1, "skip", "var-assignment", "fun-assignment", "assignments", "select", "choice", "any");
        return new Event(node.getAttributes().get("name"), parseSubstitution(node.getChildren().get(0)));
    }

}
