package icedust2.strategies.capsule;

import org.metaborg.core.MetaborgRuntimeException;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;
import io.usethesource.capsule.*;

public class immutablemap_get_0_1 extends Strategy {

    public static immutablemap_get_0_1 instance = new immutablemap_get_0_1();

    @Override
    public IStrategoTerm invoke(Context context, IStrategoTerm current, IStrategoTerm t1) {
        if (!(current instanceof StrategoImmutableMap))
            throw new MetaborgRuntimeException("Expected a StrategoImmutableMap");
        ImmutableMap<IStrategoTerm, IStrategoTerm> immutablemap = ((StrategoImmutableMap) current).immutablemap;
        return immutablemap.get(t1); // if t1 is not in the map, it returns
                                     // null, which translates to a Stratego fail
    }

}
