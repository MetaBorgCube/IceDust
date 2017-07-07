package icedust.strategies;

import org.metaborg.util.log.ILogger;
import org.metaborg.util.log.LoggerUtils;
import org.spoofax.interpreter.core.IContext;
import org.spoofax.interpreter.terms.IStrategoString;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.JavaInteropRegisterer;
import org.strategoxt.lang.Strategy;

import icedust.strategies.graph_topological_sort_1_0;

public class InteropRegisterer extends JavaInteropRegisterer {
	private static final ILogger logger = LoggerUtils.logger("Javascript interpreter");
	
	public InteropRegisterer() {
        super(new Strategy[] { 
    		  graph_topological_sort_1_0.instance 
    		, eval_javascript_0_0.instance
    		, read_resource_0_0.instance
    		, open_browser_0_0.instance
    		, make_module_tree_0_0.instance
        });
    }
    
    public void register(IContext context, Context compiledContext) {
    	super.register(context, compiledContext);
    }
}
