package icedust2.strategies.capsule;

import org.metaborg.core.MetaborgRuntimeException;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;
import io.usethesource.capsule.*;

public class immutablemap_put_0_2 extends Strategy {

    public static immutablemap_put_0_2 instance = new immutablemap_put_0_2();

    @Override
    public IStrategoTerm invoke(Context context, IStrategoTerm current, IStrategoTerm t1, IStrategoTerm t2) {
        if (!(current instanceof StrategoImmutableMap))
            throw new MetaborgRuntimeException("Expected a StrategoImmutableMap");
        ImmutableMap<IStrategoTerm, IStrategoTerm> immutablemap = ((StrategoImmutableMap) current).immutablemap;
        ImmutableMap<IStrategoTerm, IStrategoTerm> immutablemap2 = immutablemap.__put(t1, t2);
        return new StrategoImmutableMap(immutablemap2, context);
    }

}
