package pcal;

import java.util.Vector;
import pcal.exception.PcalErlangGenException;

public class PcalErlangGenerator {
	private PcalSymTab st = null;
    private AST ast = null; 
    
    public PcalErlangGenerator(PcalSymTab st, AST ast) {
    	this.st = st;
    	this.ast = ast;
    }
    
	public Vector<String> translate() throws PcalErlangGenException {
		PcalErlangGen erlangGenerator = new PcalErlangGen();
        return erlangGenerator.generate(this.ast);
	}

}
