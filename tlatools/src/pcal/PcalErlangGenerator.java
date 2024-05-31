package pcal;

import pcal.exception.PcalErlangGenException;

public class PcalErlangGenerator {
	private PcalSymTab st;
    private AST ast;
    
    public PcalErlangGenerator(PcalSymTab st, AST ast) {
    	this.st = st;
    	this.ast = ast;
    }
    
	public PcalErlangGenResult translate() throws PcalErlangGenException {
		PcalErlangGen erlangGenerator = new PcalErlangGen();
        return erlangGenerator.generate(this.ast, this.st);
	}

}
