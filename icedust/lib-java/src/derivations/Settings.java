package derivations;

public class Settings {

	static volatile boolean updatesEnabled = true;
	
	public static boolean getUpdatesEnabled(){
		return updatesEnabled;
	}
	
	public static void setUpdatesEnabled(boolean setting){
		updatesEnabled = setting;
	}
	
}
