package icedust2.strategies.capsule;

import org.metaborg.core.MetaborgRuntimeException;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

public class immutablemap_as_aterm_0_0 extends Strategy {

    public static immutablemap_as_aterm_0_0 instance = new immutablemap_as_aterm_0_0();

    @Override
    public IStrategoTerm invoke(Context context, IStrategoTerm current) {
        if (!(current instanceof StrategoImmutableMap))
            throw new MetaborgRuntimeException("Expected a StrategoImmutableMap");
        return ((StrategoImmutableMap) current).asListOfTuples();
    }

}
