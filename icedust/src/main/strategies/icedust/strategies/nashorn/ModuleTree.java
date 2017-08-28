package icedust.strategies.nashorn;

import java.util.List;

public class ModuleTree {
    public final ModuleScope root;
    public final String requireScript;
    public final List<String> externalDependencies;

    public ModuleTree(ModuleScope root, String requireScript, List<String> externalDependencies) {
        this.root = root;
        this.requireScript = requireScript;
        this.externalDependencies = externalDependencies;
    }
}
