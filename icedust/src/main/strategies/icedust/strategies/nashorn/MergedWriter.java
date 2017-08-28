package icedust.strategies.nashorn;

import java.io.IOException;
import java.io.Writer;

public class MergedWriter extends Writer{

	public final Writer lhs;
	public final Writer rhs;
	
	public MergedWriter(Writer lhs, Writer rhs) {
		this.lhs = lhs;
		this.rhs = rhs;
	}

	@Override
	public void write(char[] cbuf, int off, int len) throws IOException {
		lhs.write(cbuf, off, len);
		rhs.write(cbuf, off, len);
	}

	@Override
	public void flush() throws IOException {
		lhs.flush();
		rhs.flush();
		
	}

	@Override
	public void close() throws IOException {
		lhs.close();
		rhs.close();
	}
}
