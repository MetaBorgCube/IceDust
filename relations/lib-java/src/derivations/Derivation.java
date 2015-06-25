package derivations;

import java.util.Set;

public abstract class Derivation<E> {
	
	public abstract Set<E> dirtyValues();
	
	public abstract void cleanValues();
	
	public abstract void updateValues(Set<E> values);
	
	public boolean hasDirtyValues(){
		return !dirtyValues().isEmpty();
	}
	
	public void cleanAndUpdate(){
		Set<E> values = dirtyValues();
		cleanValues();
		updateValues(values);
	}
}
