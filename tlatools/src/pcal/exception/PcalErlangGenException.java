package pcal.exception;

import pcal.AST;

public class PcalErlangGenException extends UnrecoverablePositionedException {
	/**
     * @param message
     */
    public PcalErlangGenException(String message)
    {
        super(message);
    }

    /**
     * @param message
     * @param elementAt2
     */
    public PcalErlangGenException(String message, AST elementAt2)
    {
        super(message, elementAt2);
    }
}
