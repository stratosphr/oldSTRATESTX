package lang.eventb;

import lang.AObject;
import visitors.formatters.interfaces.IObjectFormatter;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 22:12
 */
public final class Event extends AObject {

    @Override
    public String accept(IObjectFormatter formatter) {
        return formatter.visit(this);
    }

}
