package utilities;

/**
 * Created by gvoiron on 20/11/17.
 * Time : 22:30
 */
public final class Tuple<Left, Right> {

    private final Left left;
    private final Right right;

    public Tuple(Left left, Right right) {
        this.left = left;
        this.right = right;
    }

    public Left getLeft() {
        return left;
    }

    public Right getRight() {
        return right;
    }

}
