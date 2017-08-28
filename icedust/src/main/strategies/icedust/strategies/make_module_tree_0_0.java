package icedust.strategies;

import java.io.IOException;

import org.metaborg.util.log.ILogger;
import org.metaborg.util.log.LoggerUtils;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

import icedust.strategies.nashorn.NashornInitializer;

public class make_module_tree_0_0 extends Strategy{

	private static final ILogger logger = LoggerUtils.logger("make_module");
	
	public static final make_module_tree_0_0 instance = new make_module_tree_0_0();
	
	@Override
	public IStrategoTerm invoke(Context context, IStrategoTerm current) {
		String script;
		try {
			script = NashornInitializer.makeScript(context);
			return context.getFactory().makeString(script);
		} catch (IOException e) {
			logger.error("", e);
			context.popOnFailure();
			return current;
		}
		
	}
}