package visitors.formatters.interfaces;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 01:51
 */
public interface IGenericExprFormattable {

    String accept(IGenericExprFormatter formatter);

}
