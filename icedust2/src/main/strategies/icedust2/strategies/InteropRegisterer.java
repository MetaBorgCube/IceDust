package icedust2.strategies;

import org.strategoxt.lang.JavaInteropRegisterer;
import org.strategoxt.lang.Strategy;

import icedust2.strategies.capsule.immutablemap_as_aterm_0_0;
import icedust2.strategies.capsule.immutablemap_create_0_0;
import icedust2.strategies.capsule.immutablemap_from_aterm_0_0;
import icedust2.strategies.capsule.immutablemap_get_0_1;
import icedust2.strategies.capsule.immutablemap_put_0_2;
import icedust2.strategies.capsule.is_immutablemap_0_0;

public class InteropRegisterer extends JavaInteropRegisterer {
    public InteropRegisterer() {
        super(new Strategy[] {
                graph_topological_sort_1_0.instance,
                immutablemap_as_aterm_0_0.instance,
                immutablemap_create_0_0.instance,
                immutablemap_from_aterm_0_0.instance,
                immutablemap_get_0_1.instance,
                immutablemap_put_0_2.instance,
                is_immutablemap_0_0.instance });
    }
}
