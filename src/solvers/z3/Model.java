package solvers.z3;

/**
 * Created by gvoiron on 17/11/17.
 * Time : 14:56
 */
final class Model {

    Model(com.microsoft.z3.Model model) {
        System.out.println("#####################");
        System.out.println("MODEL:");
        System.out.println("#####################");
        System.out.println(model);
        System.out.println("#####################");
    }

}
