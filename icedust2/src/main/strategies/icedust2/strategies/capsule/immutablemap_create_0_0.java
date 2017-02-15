package icedust2.strategies.capsule;

import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

import io.usethesource.capsule.DefaultTrieMap;
import io.usethesource.capsule.ImmutableMap;

public class immutablemap_create_0_0 extends Strategy {

    public static immutablemap_create_0_0 instance = new immutablemap_create_0_0();

    @Override
    public IStrategoTerm invoke(Context context, IStrategoTerm current) {
        ImmutableMap<IStrategoTerm, IStrategoTerm> immutablemap = DefaultTrieMap.of();
        return new StrategoImmutableMap(immutablemap, context);
    }

}
