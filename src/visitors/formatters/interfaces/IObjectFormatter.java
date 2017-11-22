package visitors.formatters.interfaces;

import lang.eventb.Event;
import lang.eventb.Machine;
import lang.eventb.substitutions.*;
import lang.maths.exprs.set.Enum;
import lang.maths.exprs.set.Range;
import lang.maths.exprs.set.Set;
import lang.maths.exprs.set.usuals.*;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 01:50
 */
public interface IObjectFormatter extends ISMTFormatter {

    String visit(Z z);

    String visit(ZMinus zMinus);

    String visit(ZMinusStar zMinusStar);

    String visit(ZMinusPlus zMinusPlus);

    String visit(N n);

    String visit(NPlus nPlus);

    String visit(Set set);

    String visit(Enum anEnum);

    String visit(Range range);

    String visit(Machine machine);

    String visit(Event event);

    String visit(Skip skip);

    String visit(Assignments assignments);

    String visit(VarAssignment varAssignment);

    String visit(FunAssignment funAssignment);

    String visit(Select select);

    String visit(Choice choice);

    String visit(Any any);

}
