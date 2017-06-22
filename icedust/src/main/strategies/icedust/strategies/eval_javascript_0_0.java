package icedust.strategies;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.net.URL;

import javax.script.Bindings;
import javax.script.ScriptEngine;
import javax.script.ScriptException;

import org.metaborg.util.log.ILogger;
import org.metaborg.util.log.Level;
import org.metaborg.util.log.LoggerUtils;
import org.metaborg.util.log.LoggingOutputStream;
import org.spoofax.interpreter.stratego.Fail;
import org.spoofax.interpreter.terms.IStrategoString;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

import com.coveo.nashorn_modules.Folder;
import com.coveo.nashorn_modules.Require;
//import com.coveo.nashorn_modules.ResourceFolder;

import jdk.nashorn.api.scripting.NashornScriptEngine;
import jdk.nashorn.api.scripting.NashornScriptEngineFactory;

public class eval_javascript_0_0 extends Strategy {

	private static final ILogger logger = LoggerUtils.logger("Javascript interpreter");
	
	public static final eval_javascript_0_0 instance = new eval_javascript_0_0();
	
	private NashornScriptEngine engine;
	
	private eval_javascript_0_0(){
		initializeEngine();
	}
	
	private void initializeEngine(){
		this.engine = (NashornScriptEngine) new NashornScriptEngineFactory().getScriptEngine();
		
		if(engine == null){
			logger.warn("failed to load Nashorn javascript engine");
		} else{
			logger.info("initializing Nashorn javascript engine");
			loadPolyfill();
			Writer loggeroutput = new OutputStreamWriter(new LoggingOutputStream(logger, Level.Info));
			engine.getContext().setWriter(loggeroutput);
			engine.getContext().setErrorWriter(loggeroutput);
			loadRuntime();
//			Folder folder = FixedResourceFolder.create(getClass().getClassLoader(), "lib-js", "UTF-8");
//			try {
//				Require.enable((NashornScriptEngine) engine, folder);
//			} catch (ScriptException e) {
//				logger.warn(e.getMessage());
//			}
		}
	}
	
	private void loadPolyfill(){
        loadScript("lib/nashorn-polyfill.js");
    }
	
	private void loadRuntime(){
		loadScript("dist/runtime.js");
	}
	
	private void loadScript(String path){
		try {
        	URL script = getClass().getClassLoader().getResource("lib-js/" + path);
        	engine.eval(new InputStreamReader(script.openStream()));
        } catch (ScriptException e) {
            logger.warn(e.getMessage());
        } catch (IOException e) {
        	logger.warn(e.getMessage());
		}
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
		
		final Writer w = engine.getContext().getWriter();
		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		final Writer wrapped = new OutputStreamWriter(bos); 
		Writer merged = new Writer() {
			@Override
			public void write(char[] cbuf, int off, int len) throws IOException {
				w.write(cbuf, off, len);
				wrapped.write(cbuf, off, len);
			}
			
			@Override
			public void flush() throws IOException {
				w.flush();
				wrapped.flush();
			}
			
			@Override
			public void close() throws IOException {
				w.close();
				wrapped.close();
			}
		};
		
		String output = "";
		if(engine == null){
			logger.warn("could not execute, javascript engine was not properly loaded.");
		} else{
			try {
				engine.getContext().setWriter(merged);
				engine.eval(program);
				engine.getContext().setWriter(w);
				output = new String(bos.toByteArray());
			} catch (Exception e) {
				logger.warn(e.getMessage());
			}
		}
		return context.getFactory().makeString(output);
	}
	
}
