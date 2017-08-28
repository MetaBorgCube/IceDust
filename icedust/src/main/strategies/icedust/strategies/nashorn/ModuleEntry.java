package icedust.strategies.nashorn;

public class ModuleEntry {
    public final String name;
    public final String content;

    public ModuleEntry(String name, String content) {
        this.name = name;
        this.content = content;
    }

    @Override
    public String toString() {
        return "ModuleEntry{" +
                "name='" + name + '\'' +
                ", content='" + content + '\'' +
                '}';
    }
}
