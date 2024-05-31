package pcal;

import java.util.Vector;

public class PcalErlangGenResult {
    private final Vector<String> code;

    public PcalErlangGenResult(Vector<String> code) {
        this.code = code;
    }

    public Vector<String> getCode() {
        return code;
    }
}
