package icedust.strategies;

import com.coveo.nashorn_modules.AbstractFolder;
import com.coveo.nashorn_modules.Folder;
import org.apache.commons.io.IOUtils;

import java.io.IOException;
import java.io.InputStream;

public class FixedResourceFolder extends AbstractFolder {
    private ClassLoader loader;
    private String resourcePath;
    private String encoding;

    public String getFile(String name) {
        InputStream stream = loader.getResourceAsStream(resourcePath + "/" + name);
        if (stream == null) {
            return null;
        }

        try {
            return IOUtils.toString(stream, encoding);
        } catch (IOException ex) {
            return null;
        } catch(NullPointerException e){
            return null;
        }
    }

    public Folder getFolder(String name) {
        return new FixedResourceFolder(
                loader, resourcePath + "/" + name, this, getPath() + name + "/", encoding);
    }

    private FixedResourceFolder(
            ClassLoader loader, String resourcePath, Folder parent, String displayPath, String encoding) {
        super(parent, displayPath);
        this.loader = loader;
        this.resourcePath = resourcePath;
        this.encoding = encoding;
    }

    public static FixedResourceFolder create(ClassLoader loader, String path, String encoding) {
        return new FixedResourceFolder(loader, path, null, "/", encoding);
    }
}
