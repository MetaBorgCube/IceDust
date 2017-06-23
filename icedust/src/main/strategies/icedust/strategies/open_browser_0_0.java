package icedust.strategies;

import java.io.File;
import java.io.IOException;
import java.util.Locale;

import org.metaborg.util.log.ILogger;
import org.metaborg.util.log.LoggerUtils;
import org.spoofax.interpreter.terms.IStrategoString;
import org.spoofax.interpreter.terms.IStrategoTerm;
import org.strategoxt.lang.Context;
import org.strategoxt.lang.Strategy;

public class open_browser_0_0 extends Strategy{
    private final ILogger logger = LoggerUtils.logger(getClass());
    
    public static final open_browser_0_0 instance = new open_browser_0_0();
    
    private open_browser_0_0() {
        
    }
    
    @Override
    public IStrategoTerm invoke(Context context, IStrategoTerm current) {
      if(current.getTermType() == IStrategoTerm.STRING){
        String path = ((IStrategoString) current).stringValue();
        if(!path.endsWith(".html")){
          logger.warn("file is not an html file: " + path);
          return current;
        }
        
        File f = new File(path);
        if(!f.exists()){
          logger.warn("file not found: " + f.getAbsolutePath());
          return current;
        }
      
        try {
          String cmd;
          String os = System.getProperty("os.name", "generic").toLowerCase(Locale.ENGLISH);
          if ((os.indexOf("mac") >= 0) || (os.indexOf("darwin") >= 0)) {
            cmd = "open";
          } else if (os.indexOf("win") >= 0) {
            cmd = "cmd /c start";
          } else if (os.indexOf("nux") >= 0) {
            cmd = "xdg-open";
          } else {
            cmd = "open";
          }
          Runtime.getRuntime().exec(new String[]{cmd, f.getAbsolutePath()});
        } catch (IOException e) {
          logger.warn(e.getMessage());
        }
      }
      return current;
    }
}