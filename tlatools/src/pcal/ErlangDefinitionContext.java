package pcal;

import pcal.exception.PcalErlangGenException;

import java.util.Map;
import java.util.Vector;

public class ErlangDefinitionContext extends ErlangProcessContext {

    public ErlangDefinitionContext(String processName, Map<String, String> constants) throws PcalErlangGenException {
        super(processName, new Vector<String>());
        for (String constant : constants.keySet()) {
            addDefinition(constant);
        }
    }

    public void addDefinition(String pcalName) throws PcalErlangGenException {
        this.stateFieldNames.put(pcalName, new ErlangStateField(pcalName, ErlangStateField.FieldType.CONSTANT));
    }

}
