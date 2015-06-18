package derivations;

import java.util.List;

public class Scheduler {
	
	private List<List<Derivation<Object>>> ordering;
	
	public void setDerivations(List<List<Derivation<Object>>> ordering){
		this.ordering = ordering;
	}
	
	public void updateDerivations(){
		for (List<Derivation<Object>> derivationGroup : ordering){
			boolean anyDirty;
			do{
				for(Derivation<Object> derivation : derivationGroup){
					derivation.cleanAndUpdate();
				}
				anyDirty = false;
				for(Derivation<Object> derivation : derivationGroup){
					if(derivation.hasDirtyValues()){
						anyDirty = true;
					}
				}
			}while(anyDirty);
		}
	}
	
}
