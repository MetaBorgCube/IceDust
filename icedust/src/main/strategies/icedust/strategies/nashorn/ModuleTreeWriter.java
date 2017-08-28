package icedust.strategies.nashorn;

import java.io.IOException;

public class ModuleTreeWriter {

    private ModuleTree tree;
    private StringBuilder builder;

    private ModuleTreeWriter(ModuleTree tree) {
        this.tree = tree;
        this.builder = new StringBuilder();
    }

    public String writeTree() throws IOException {
        this.builder = new StringBuilder();
        builder.append("var Require = "); builder.append(wrapCommonJS(tree.requireScript)); newline();
        writeRoot(); newline();
        tree.root.subScopes.values().forEach(this::writeScope);
        writeEagerEval();
        writeRootRequire();
        return wrapCommonJS(builder.toString());
    }

    private void newline(){
        builder.append("\n");
    }

    private void writeRoot(){
        builder.append("var root = Require.makeRoot();"); newline();
        writeEntries(tree.root);
        writeExternalDeps();
    }

    private void writeExternalDeps(){
        for(int i = 0 ; i < tree.externalDependencies.size() ; i++){
            String varName = "external_" + i;
            builder.append("var ").append(varName).append(" = ").append(wrapCommonJS(tree.externalDependencies.get(i))); newline();
            builder.append("Object.keys(").append(varName).append(").forEach(function(key){")
                    .append(tree.root.name).append(".entries[key] = Require.lazyConst(").append(varName).append("[key])")
                    .append("});");newline();
        }
    }

    private void writeEagerEval(){
        builder.append("module.exports['Runtime'] = Require.eagerlyLoadModules(root);"); newline();
    }
    
    private void writeRootRequire(){
    	builder.append("module.exports['require'] = root.require;"); newline();
    }

    private void writeEntries(ModuleScope scope){
        scope.entries.values().forEach(entry -> {
            builder.append(scope.name).append(".entries['").append(entry.name).append("'] = ")
                    .append("Require.lazyModule(function(require, module){\n")
                    .append(entry.content)
                    .append("\n")
                    .append("return module;\n")
                    .append("}")
                    .append(", ")
                    .append(scope.name)
                    .append(");"); newline();
        });
    }

    public void writeScope(ModuleScope scope){
        builder.append("var ")
                .append(scope.name)
                .append(" = ")
                .append("Require.makeScope('")
                .append(scope.name)
                .append("', ")
                .append("root, ")
                .append(scope.parent == null ? "root" : scope.parent.name)
                .append(")")
                .append(";\n");
        writeEntries(scope);
        scope.subScopes.values().forEach(this::writeScope);
    }

    private String wrapCommonJS(String module){
        return
                "(function(){\nvar module = {exports: {}};\n(function(module){\n"
                        + module
                        + " \nreturn module;\n})(module);\nreturn module.exports;\n})();";
    }


    public static String writeTree(ModuleTree tree) throws IOException {
        return new ModuleTreeWriter(tree).writeTree();
    }
}
