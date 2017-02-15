package icedust2.strategies.capsule;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;

import org.spoofax.interpreter.terms.IStrategoList;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.spoofax.interpreter.terms.IStrategoTuple;
import org.spoofax.interpreter.terms.ITermPrinter;
import org.spoofax.terms.attachments.ITermAttachment;
import org.spoofax.terms.attachments.TermAttachmentType;
import org.strategoxt.lang.Context;

import io.usethesource.capsule.ImmutableMap;

public class StrategoImmutableMap implements IStrategoTerm {

    public final ImmutableMap<IStrategoTerm, IStrategoTerm> immutablemap;
    public final Context context;

    public StrategoImmutableMap(ImmutableMap<IStrategoTerm, IStrategoTerm> immutablemap, Context context) {
        this.immutablemap = immutablemap;
        this.context = context;
    }

    public IStrategoList asListOfTuples() {
        List<IStrategoTerm> keys = new ArrayList<>(immutablemap.keySet());

        Comparator<IStrategoTerm> comparator = new Comparator<IStrategoTerm>() {
            @Override
            public int compare(IStrategoTerm left, IStrategoTerm right) {
                return left.toString().compareToIgnoreCase(right.toString());
            }
        };
        Collections.sort(keys, comparator);

        List<IStrategoTuple> tuples = new ArrayList<IStrategoTuple>();
        for (IStrategoTerm key : keys) {
            IStrategoTerm value = immutablemap.get(key);
            IStrategoTuple tuple = context.getFactory().makeTuple(key, value);
            tuples.add(tuple);
        }
        IStrategoList list = context.getFactory().makeList(tuples);
        return list;
    }

    /**
     * 
     */
    private static final long serialVersionUID = 525602895475606855L;

    @Override
    public <T extends ITermAttachment> T getAttachment(TermAttachmentType<T> arg0) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public boolean isList() {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public void putAttachment(ITermAttachment arg0) {
        // TODO Auto-generated method stub

    }

    @Override
    public ITermAttachment removeAttachment(TermAttachmentType<?> arg0) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Iterator<IStrategoTerm> iterator() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public IStrategoTerm[] getAllSubterms() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public IStrategoList getAnnotations() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public int getStorageType() {
        // TODO Auto-generated method stub
        return 0;
    }

    @Override
    public IStrategoTerm getSubterm(int arg0) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public int getSubtermCount() {
        // TODO Auto-generated method stub
        return 0;
    }

    @Override
    public int getTermType() {
        return IStrategoTerm.BLOB;
    }

    @Override
    public boolean match(IStrategoTerm arg0) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public void prettyPrint(ITermPrinter arg0) {
        // TODO Auto-generated method stub
    }

    @Override
    public String toString(int arg0) {
        return asListOfTuples().toString();
    }

    @Override
    public void writeAsString(Appendable arg0, int arg1) throws IOException {
        asListOfTuples().writeAsString(arg0, arg1);
    }

}
