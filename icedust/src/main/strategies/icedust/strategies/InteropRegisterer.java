package icedust.strategies;

import org.strategoxt.lang.JavaInteropRegisterer;
import org.strategoxt.lang.Strategy;

import icedust.strategies.graph_topological_sort_1_0;

public class InteropRegisterer extends JavaInteropRegisterer {
    public InteropRegisterer() {
        super(new Strategy[] { graph_topological_sort_1_0.instance });
    }
}
