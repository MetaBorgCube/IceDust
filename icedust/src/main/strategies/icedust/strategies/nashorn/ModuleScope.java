package icedust.strategies.nashorn;

import java.util.HashMap;
import java.util.Map;

public class ModuleScope {
    public final String name;
    public final ModuleScope parent;
    public final Map<String, ModuleScope> subScopes;
    public final Map<String, ModuleEntry> entries;

    public ModuleScope(String name, ModuleScope parent, Map<String, ModuleScope> subScopes, Map<String, ModuleEntry> entries) {
        this.name = name;
        this.parent = parent;
        this.subScopes = subScopes;
        this.entries = entries;
    }

    public ModuleScope(String name, ModuleScope parent) {
        this(name, parent, new HashMap<>(), new HashMap<>());
    }

    @Override
    public String toString() {
        return "ModuleScope{" +
                "name='" + name + '\'' +
                ", subScopes=" + subScopes +
                ", entries=" + entries +
                '}';
    }

    public boolean isRoot(){
        return this.parent == null;
    }
}
