package icedust.strategies;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.Arrays;

import javax.script.Bindings;
import javax.script.ScriptEngine;
import javax.script.ScriptException;

import org.metaborg.core.resource.IResourceService;
import org.metaborg.spoofax.core.Spoofax;
import org.metaborg.util.log.ILogger;
import org.metaborg.util.log.Level;
import org.metaborg.util.log.LoggerUtils;
import org.metaborg.util.log.LoggingOutputStream;
import org.spoofax.interpreter.stratego.Fail;
import org.spoofax.interpreter.terms.IStrategoList;
import org.spoofax.interpreter.terms.IStrategoString;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.spoofax.interpreter.terms.IStrategoTuple;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

import com.coveo.nashorn_modules.Paths;
import com.google.common.io.Resources;

import icedust.strategies.nashorn.MergedWriter;
import icedust.strategies.nashorn.NashornInitializer;

//import com.coveo.nashorn_modules.ResourceFolder;

import jdk.nashorn.api.scripting.NashornScriptEngine;
import jdk.nashorn.api.scripting.NashornScriptEngineFactory;

public class eval_javascript_0_0 extends Strategy {
	private static final ILogger logger = LoggerUtils.logger("Javascript interpreter");

	public static final eval_javascript_0_0 instance = new eval_javascript_0_0();
	
	
	private String evalAndCaptureOutput(ScriptEngine engine, String program) throws ScriptException{
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		MergedWriter merged = new MergedWriter(engine.getContext().getWriter(), new OutputStreamWriter(bos));
		engine.getContext().setWriter(merged);
		engine.eval(program);
		engine.getContext().setWriter(merged.lhs);
		return new String(bos.toByteArray());
	} 
	
	@Override
	public IStrategoTerm invoke(Context context, IStrategoTerm current) {
		String program = null;
		if(current.getTermType() == IStrategoTerm.STRING){
			program = ((IStrategoString) current).stringValue();
		} else {
			IStrategoTerm ppJsTerm = context.invokeStrategy("pp-js-program", current);
			program = ((IStrategoString) ppJsTerm).stringValue();
		}
		ScriptEngine engine = NashornInitializer.getInstance(context);
		try {
			String result = evalAndCaptureOutput(engine, program);
			return context.getFactory().makeString(result);
		} catch (ScriptException e) {
			logger.error("", e);
			context.popOnFailure();
			return current;
		}
	}
	
}
