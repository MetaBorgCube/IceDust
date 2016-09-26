package icedust2.strategies;

import org.strategoxt.lang.JavaInteropRegisterer;
import org.strategoxt.lang.Strategy;

import icedust2.strategies.graph_topological_sort_1_0;

public class InteropRegisterer extends JavaInteropRegisterer {
    public InteropRegisterer() {
        super(new Strategy[] { graph_topological_sort_1_0.instance });
    }
}
