package lang;

import visitors.formatters.ObjectFormatter;
import visitors.formatters.interfaces.IObjectFormattable;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 01:44
 */
public abstract class AObject implements IObjectFormattable, Comparable<AObject> {

    private Integer hashCode;

    protected AObject() {
        this.hashCode = null;
    }

    @Override
    public int hashCode() {
        if (hashCode == null) {
            hashCode = toString().hashCode();
        }
        return hashCode;
    }

    @Override
    public boolean equals(Object o) {
        return getClass().equals(o.getClass()) && hashCode() == o.hashCode();
    }

    @Override
    public int compareTo(AObject object) {
        return toString().compareTo(object.toString());
    }

    @Override
    public final String toString() {
        return accept(new ObjectFormatter());
    }

}
