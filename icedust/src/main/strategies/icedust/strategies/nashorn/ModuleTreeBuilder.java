package icedust.strategies.nashorn;

import org.apache.commons.io.FilenameUtils;
import org.apache.commons.io.IOUtils;
import org.metaborg.util.log.ILogger;
import org.metaborg.util.log.LoggerUtils;
import org.spoofax.interpreter.core.InterpreterException;
import org.spoofax.interpreter.library.IOAgent;
import org.strategoxt.lang.Context;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.net.MalformedURLException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class ModuleTreeBuilder {

	private static final ILogger logger = LoggerUtils.logger(ModuleTreeBuilder.class);
	
	private final Context context;
	private final IOAgent io;
	private final String rootPath;
	private final String requireScript;
	private final List<String> externalDependencies;
    private ModuleScope rootScope;

    
    private ModuleTreeBuilder(Context context, String rootPath, String requireScript, List<String> externalDependencies) {
        this.context = context;
    	this.rootPath = rootPath;
    	this.requireScript = requireScript;
        this.externalDependencies = externalDependencies;
        this.io = context.getIOAgent();
        rootScope = new ModuleScope("root", null);
    }
    
    public static ModuleTree makeTree(Context context, String rootPath, String requireScript, String... externalDeps){
    	return new ModuleTreeBuilder(context, rootPath, requireScript, Arrays.asList(externalDeps)).build();
    }
    
    public ModuleTree build(){
    	ModuleScope root = new ModuleScope("root", null);
    	for(String sub : io.readdir(rootPath)){
    		String fullPath = rootPath + "/" + sub;
    		if(io.isDirectory(fullPath)){
    			processScope(root, fullPath);
    		} else if(fullPath.endsWith(".js")){
    			processEntry(root, fullPath);
    		}
    	}
    	return new ModuleTree(root, requireScript, readDepedencies());
    }
    
    private List<String> readDepedencies(){
    	List<String> result = new ArrayList<>();
    	for(String dep : externalDependencies){
    		try{
    			int fd = io.openRandomAccessFile(dep, "r");
    			result.add(io.readString(fd));
    			io.closeRandomAccessFile(fd);
    		} catch(InterpreterException | IOException e){
    			logger.warn("could not load external dependency: " + dep + " : " + e.getMessage());
    		}
			
    	}
    	return result;
    }
    
    private void processScope(ModuleScope parent, String dir){
    	String scopeName = FilenameUtils.getBaseName(dir);
    	ModuleScope scope = new ModuleScope(scopeName, parent);
    	for(String sub : io.readdir(dir)){
    		String fullPath = dir + "/" + sub;
    		if(io.isDirectory(fullPath)){
    			processScope(scope, fullPath);
    		} else if(fullPath.endsWith(".js")){
    			processEntry(scope, fullPath);
    		}
    	}
    	parent.subScopes.put(scopeName, scope);
    }
    
    private void processEntry(ModuleScope parent, String file){
    	String entryName = FilenameUtils.getBaseName(file);
    	try{
    		int fd = context.getIOAgent().openRandomAccessFile(file, "r");
    		String content = context.getIOAgent().readString(fd);
        	context.getIOAgent().closeRandomAccessFile(fd);
        	ModuleEntry entry = new ModuleEntry(entryName, content);
        	parent.entries.put(entryName, entry);
    	} catch(InterpreterException | IOException e){
    		logger.error(e.getMessage());
    		e.printStackTrace();
    	}
    }
}
