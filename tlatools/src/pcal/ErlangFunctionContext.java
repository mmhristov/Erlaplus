package pcal;

import pcal.exception.PcalErlangGenException;

import java.util.*;

public class ErlangFunctionContext extends ErlangProcessContext {

    private Map<String,String> functionVars;

    public ErlangFunctionContext(ErlangProcessContext context, List<String> functionVars) {
        super(context, true);
        this.functionVars = new HashMap<>();
        for (String var :functionVars
        ) {
            this.functionVars.put(var, "FunctionVar_" + var);
        }
    }


    /**
     * Gets the variable name given a PlusCal variable name. The name can either be a state variable or a record key name.
     * @param pcalVarName The variable name in PlusCal.
     * @return The variable name string.
     */
    public String getErlangVarStr(String pcalVarName) throws PcalErlangGenException {
        String res = this.functionVars.get(pcalVarName);
        if(res != null){
            return res;
        }
        return super.getErlangVarStr(pcalVarName);
    }
}