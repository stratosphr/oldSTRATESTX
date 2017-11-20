package lang.maths.exprs.set.usuals;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 11:09
 */
public final class UsualSetFabric {

    private static final N n = new N();
    private static final NPlus nPlus = new NPlus();
    private static final Z z = new Z();
    private static final ZMinus zMinus = new ZMinus();
    private static final ZMinusPlus zMinusPlus = new ZMinusPlus();
    private static final ZMinusStar zMinusStar = new ZMinusStar();

    public static AUsualSet getUsualSet(EUsualSet usualSet) {
        switch (usualSet) {
            case N:
                return n;
            case N_PLUS:
                return nPlus;
            case Z:
                return z;
            case Z_MINUS:
                return zMinus;
            case Z_MINUS_PLUS:
                return zMinusPlus;
            case Z_MINUS_STAR:
                return zMinusStar;
        }
        throw new Error("Error: unable to build unknown usual set \"" + usualSet + "\".");
    }

}
