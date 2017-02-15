package icedust2.strategies.capsule;

import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

public class is_immutablemap_0_0 extends Strategy {

    public static is_immutablemap_0_0 instance = new is_immutablemap_0_0();

    @Override
    public IStrategoTerm invoke(Context context, IStrategoTerm current) {
        if (!(current instanceof StrategoImmutableMap))
            return null; // is Stratego fail
        return current;
    }

}
