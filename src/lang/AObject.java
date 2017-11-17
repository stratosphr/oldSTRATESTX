package lang;

import visitors.formatters.ObjectFormatter;
import visitors.formatters.interfaces.IObjectFormattable;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 01:44
 */
public abstract class AObject implements IObjectFormattable {

    @Override
    public final String toString() {
        return accept(new ObjectFormatter());
    }

}
