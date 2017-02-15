package icedust2.strategies.capsule;

import org.metaborg.core.MetaborgRuntimeException;
import org.spoofax.interpreter.terms.IStrategoList;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.spoofax.interpreter.terms.IStrategoTuple;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

import io.usethesource.capsule.DefaultTrieMap;
import io.usethesource.capsule.ImmutableMap;

public class immutablemap_from_aterm_0_0 extends Strategy {

    public static immutablemap_from_aterm_0_0 instance = new immutablemap_from_aterm_0_0();

    @Override
    public IStrategoTerm invoke(Context context, IStrategoTerm current) {
        if (!(current instanceof IStrategoList))
            throw new MetaborgRuntimeException("Expected a IStrategoList, got: " + current.toString());
        IStrategoList list = ((IStrategoList) current);
        ImmutableMap<IStrategoTerm, IStrategoTerm> immutablemap = DefaultTrieMap.of();
        for (IStrategoTerm elem : list) {
            if (!(elem instanceof IStrategoTuple))
                throw new MetaborgRuntimeException("Expected a IStrategoTuple, got: " + elem.toString());
            IStrategoTuple tuple = (IStrategoTuple) elem;
            if (tuple.size() != 2)
                throw new MetaborgRuntimeException("Expected a IStrategoTuple of size 2, got size: " + tuple.size());
            IStrategoTerm key = tuple.get(0);
            IStrategoTerm value = tuple.get(1);
            immutablemap = immutablemap.__put(key, value);
        }
        return new StrategoImmutableMap(immutablemap, context);
    }

}
