package parsers.ebm;

import lang.eventb.Event;
import lang.eventb.Machine;
import lang.eventb.substitutions.ASubstitution;
import lang.maths.defs.DefsContext;
import lang.maths.defs.FunDef;
import lang.maths.defs.VarDef;
import lang.maths.exprs.arith.*;
import lang.maths.exprs.bool.ABoolExpr;
import lang.maths.exprs.bool.Equals;
import lang.maths.exprs.bool.False;
import lang.maths.exprs.set.ASetExpr;
import lang.maths.exprs.set.Enum;
import lang.maths.exprs.set.Range;
import lang.maths.exprs.set.Set;
import lang.maths.exprs.set.usuals.UsualSetFabric;
import parsers.xml.XMLNode;
import parsers.xml.XMLParser;
import solvers.z3.Z3;
import solvers.z3.Z3Result;
import utilities.ResourcesManager;
import utilities.Tuple;

import java.io.File;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

import static lang.maths.exprs.set.usuals.EUsualSet.Z;
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
            // TODO: UPDATE SCHEMA TO MAKE CONSTS COME BEFORE SETS SINCE SETS CAN USE CONSTS
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
            LinkedHashSet<FunDef> funsDefs = parseFunsDefs(funsDefsNode);
            ABoolExpr invariant = parseInvariant(invariantNode);
            ASubstitution initialisation = parseInitialisation(initialisationNode);
            LinkedHashSet<Event> events = parseEvents(eventsNode);
            varsDefs.forEach(System.out::println);
            funsDefs.forEach(System.out::println);
            return new Machine();
        } catch (Exception e) {
            throw new Error(e);
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

    private Tuple<String, AArithExpr> parseConstDef(XMLNode node) {
        node.assertConformsTo("const-def", 1, 1, "int", "const", "var", "fun", "plus", "minus", "times", "div", "mod");
        AArithExpr expr = parseArithExpr(node.getChildren().get(0));
        DefsContext tmpDefsContext = new DefsContext();
        if (!expr.getFuns(tmpDefsContext).isEmpty() || !expr.getVars(tmpDefsContext).isEmpty()) {
            throw new Error("Error l." + node.getChildren().get(0).getLine() + ",c." + node.getColumn() + ": the value of a const (here \"" + node.getAttributes().get("name") + "\") cannot depend on any variable or function.");
        }
        Var valueVar = new Var("value!");
        defsContext.getConstsDefs().forEach(tmpDefsContext::addDef);
        tmpDefsContext.addDef(new VarDef<>(valueVar.getName(), UsualSetFabric.getUsualSet(Z)));
        Z3Result result = Z3.checkSAT(new Equals(valueVar, expr), tmpDefsContext);
        if (result.isSAT()) {
            defsContext.addDef(node.getAttributes().get("name"), result.getModel().get(valueVar));
            return new Tuple<>(node.getAttributes().get("name"), expr);
        } else {
            throw new Error("Error l." + node.getChildren().get(0).getLine() + ",c." + node.getColumn() + ": unable to compute the value of const \"" + node.getAttributes().get("name") + "\" with expression \"" + expr + "\".");
        }
    }

    private LinkedHashMap<String, ASetExpr> parseSetsDefs(XMLNode node) {
        LinkedHashMap<String, ASetExpr> setsDefs = new LinkedHashMap<>();
        if (node != null) {
            node.assertConformsTo("sets-defs", 1, -1, "set-def");
        }
        return setsDefs;
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
        if (domain.isEmpty()) {
            throw new Error("Error l." + node.getLine() + ",c." + node.getColumn() + ": the domain of a variable (here \"" + node.getAttributes().get("name") + "\") cannot be empty (here " + domain + ").");
        }
        return new VarDef<>(node.getAttributes().get("name"), domain);
    }

    private LinkedHashSet<FunDef> parseFunsDefs(XMLNode node) {
        LinkedHashSet<FunDef> funsDefs = new LinkedHashSet<>();
        if (node != null) {
            node.assertConformsTo("funs-defs", 1, -1, "fun-def");
        }
        return funsDefs;
    }

    private ABoolExpr parseInvariant(XMLNode node) {
        return parseBoolExpr(node);
    }

    private ASubstitution parseInitialisation(XMLNode node) {
        return null;
    }

    private LinkedHashSet<Event> parseEvents(XMLNode node) {
        return null;
    }

    private AArithExpr parseArithExpr(XMLNode node) {
        switch (node.getName()) {
            case "int":
                return parseInt(node);
            case "const":
                return parseConst(node);
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
        }
        throw new Error("Error l." + node.getLine() + ",c." + node.getColumn() + ": unable to parse the following unknown arithmetic expression:\n" + node);
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

    // TODO : MOD IN Z3 ONLY TAKES 2 PARAMETERS, FIX THE Mod CLASS
    private AArithExpr parseMod(XMLNode node) {
        throw new Error("Unhandled case mod");
    }

    private ABoolExpr parseBoolExpr(XMLNode node) {
        return new False();
    }

    private ASetExpr parseSetExpr(XMLNode node) {
        switch (node.getName()) {
            case "usual":
                return parseUsualSet(node);
            case "named-set":
                return parseNamedSet(node);
            case "set":
                return parseSet(node);
            case "enum":
                return parseEnum(node);
            case "range":
                return parseRange(node);
        }
        throw new Error("Error l." + node.getLine() + ",c." + node.getColumn() + ": unable to parse the following unknown set expression:\n" + node);
    }

    private ASetExpr parseUsualSet(XMLNode node) {
        node.assertConformsTo("usual", 0, 0);
        System.err.println("Warning: parsing returns finite set by default for the moment, this must be fixed.");
        return new Set(new Int(0));
    }

    // TODO : FIX CUSTOM WARNINGS
    private ASetExpr parseNamedSet(XMLNode node) {
        node.assertConformsTo("range", 2, 2, "int", "const", "plus", "minus", "times", "div", "mod");
        System.err.println("Warning: parsing returns finite set by default for the moment, this must be fixed.");
        return new Set(new Int(0));
    }

    // TODO : PRECISE REAL RETURN TYPE
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

}
