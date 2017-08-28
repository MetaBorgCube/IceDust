package icedust.strategies.nashorn;

import jdk.nashorn.api.scripting.NashornScriptEngineFactory;
import jdk.nashorn.api.scripting.ScriptObjectMirror;

import org.metaborg.util.log.ILogger;
import org.metaborg.util.log.Level;
import org.metaborg.util.log.LoggerUtils;
import org.metaborg.util.log.LoggingOutputStream;
import org.spoofax.interpreter.core.InterpreterException;
import org.spoofax.interpreter.terms.IStrategoString;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

import javax.script.ScriptEngine;
import javax.script.ScriptException;
import java.io.*;
import java.net.URISyntaxException;

public class NashornInitializer {
	
	public static final String SOURCE_FOLDER = "lib-js/src/runtime";
	public static final String DEPENDENCIES_FILE = "lib-js/dependencies/target/libraries.generated.js";
	public static final String POLYFILL_FILE = "lib-js/src/nashorn-polyfill.js";
	public static final String REQUIRE_FILE = "lib-js/src/require.js";
	
	
	
	private static final ILogger logger = LoggerUtils.logger(NashornInitializer.class);

    private static ScriptEngine engine;

    
    private Context context;
    private String componentPath;
    
    private NashornInitializer(Context context){
    	this.context = context;
    	setComponentPath();
    }
    
    private void setComponentPath(){
    	Strategy[] sargs = new Strategy[]{};
		IStrategoTerm[] targs = new IStrategoString[]{};
		IStrategoTerm term = null;
		IStrategoTerm res = context.invokePrimitive("language_components", term, sargs, targs);
		this.componentPath = ((IStrategoString) res.getSubterm(0).getSubterm(3)).stringValue();
    }
    
    public static ScriptEngine getInstance(Context context){
        if(engine == null){
            engine = new NashornInitializer(context).initialize();
        }
        return engine;
    }

    private ScriptEngine initialize(){
    	logger.info("initializing Nashorn engine");
        ScriptEngine engine = new NashornScriptEngineFactory().getScriptEngine();
        setEngineOutput(engine);
        try{
            loadPolyfill(engine);
            loadModules(engine);
        } catch(IOException | ScriptException e) {
            logger.error("Nashorn engine initialization", e);
        }
        return engine;
    }
    
    private void setEngineOutput(ScriptEngine engine){
    	Writer loggeroutput = new OutputStreamWriter(new LoggingOutputStream(logger, Level.Info));
		engine.getContext().setWriter(loggeroutput);
		engine.getContext().setErrorWriter(loggeroutput);
    }
    

    private void loadPolyfill(ScriptEngine engine) throws ScriptException {
        try{
	    	int fd = context.getIOAgent().openRandomAccessFile(componentPath + "/" + POLYFILL_FILE, "r");
	    	String polyfill = context.getIOAgent().readString(fd);
	    	context.getIOAgent().closeRandomAccessFile(fd);
	    	engine.eval(polyfill);
        } catch(InterpreterException | IOException e){
        	logger.error(e.getMessage());
        	e.printStackTrace();
        }
    }
    
    private String readRequireScript() {
    	try{
	    	int fd = context.getIOAgent().openRandomAccessFile(componentPath + "/" + REQUIRE_FILE, "r");
	    	String requireScript = context.getIOAgent().readString(fd);
	    	context.getIOAgent().closeRandomAccessFile(fd);
	    	return requireScript;
        } catch(InterpreterException | IOException e){
        	logger.error(e.getMessage());
        	e.printStackTrace();
        	return null;
        }
    }

    private void loadModules(ScriptEngine engine) throws IOException, ScriptException {
        String script = makeScript();
        ScriptObjectMirror runtime = (ScriptObjectMirror) engine.eval(script);
        runtime.forEach(engine::put);
    }
    
    public String makeScript() throws IOException{
    	ModuleTree tree = ModuleTreeBuilder.makeTree(context, componentPath + "/" + SOURCE_FOLDER, readRequireScript(), componentPath + "/" + DEPENDENCIES_FILE);
        String script = ModuleTreeWriter.writeTree(tree);
        return script;
    }
    
    public static String makeScript(Context context) throws IOException{
    	return new NashornInitializer(context).makeScript();
    }
}
