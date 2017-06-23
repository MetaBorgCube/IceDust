package icedust.strategies;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.net.URL;
import java.nio.charset.Charset;

import org.apache.commons.io.IOUtils;
import org.metaborg.util.log.ILogger;
import org.metaborg.util.log.LoggerUtils;
import org.spoofax.interpreter.terms.IStrategoString;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

public class read_resource_0_0 extends Strategy{
	private final ILogger logger = LoggerUtils.logger(getClass());
	
	public static final read_resource_0_0 instance = new read_resource_0_0();
	
	private read_resource_0_0() {
		
	}
	
	@Override
	public IStrategoTerm invoke(Context context, IStrategoTerm current) {
		if(current.getTermType() == IStrategoTerm.STRING){
			String resourcePath = ((IStrategoString) current).stringValue();
			try {
				String resourceContents = loadResourceAsString(context, resourcePath);
				IStrategoString result = context.getFactory().makeString(resourceContents);
				return result;
			} catch(IOException e) {
				logger.warn(e.getMessage());
				context.popOnFailure();
				return current;
			}
			
		} else{
			logger.warn("expected String argument");
			context.popOnFailure();
			return current;
		}
	}
	
	private String loadResourceAsString(Context context, String resource) throws IOException{
		URL url = getClass().getClassLoader().getResource(resource);
		if(url == null){
			throw new FileNotFoundException(resource);
		} else {
			return IOUtils.toString(url.openStream(), Charset.defaultCharset());
		}
	}
	
	
}