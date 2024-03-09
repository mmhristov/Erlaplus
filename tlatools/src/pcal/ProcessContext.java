package pcal;

import pcal.exception.PcalErlangGenException;

import java.util.*;

import static pcal.PCalErlangConstants.*;

/*
    todo: might be a good idea to create some sub-classes of ProcessContext in order to encapsulate
     different kinds of contexts and reduce cluttering in this class.
 */
public class ProcessContext {

    /**
     * Signifies whether the context is currently in a variable declaration scope.
     * Set the flag only when variable declarations are currently being parsed.
     */
    private boolean isInVarDeclScope = false;

    private final String processName;

    private int stateVarNum = 0;

    private int messageVarNum = 0;

    private String currentStateVarName;

    private String currentMessageVarName;

    private final String stateRecordName;

    private static int whileNum = 0;

    /**
     * A mapping of PlusCal process-local variable names to erlang variable names.
     * This map corresponds to the process state in erlang, which includes all variable declarations.
     */
    private final TreeMap<String, String> fieldNames;

    /**
     * A mapping of PlusCal temporary variables (i.e. variables that are not part of the state) to erlang variable names.
     */
    private final TreeMap<String, String> temporaryVarNames = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);

    /**
     * A process-local history of all generated temporary variables.
     * Currently temporary variables are ones that
     *  are initialized via PlusCal's "with" statement.
     */
    private final TreeMap<String, Integer> temporaryVarsHistory = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);

    private int recordScopeDepth = 0;

    public ProcessContext(String processName, Vector fieldVarDecls) {
        this.processName = createProcessName(processName);
        this.stateRecordName = PREFIX_PROCESS_STATE_NAME + processName;
        stateVarNum = 0;
        messageVarNum = 0;
        setCurrentStateVarName();
        setCurrentMessageVarNum();
        /*
          We use case-insensitive comparators since PlusCal variable names are case-insensitive!
         */
        this.fieldNames = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);
        fillFieldNames(fieldVarDecls);
    }

    private static String createProcessName(String processName) {
        return PREFIX_PROCESS + processName;
    }

    /**
     * Creates a copy of the provided context, which is filled depending on whether a new Erlang scope is entered or not.
     * In the case of entering a new scope (e.g. when entering a new erlang function),
     *  the state variable counter and the message variable counter are reset, and
     * @param context The context to be copied from.
     */
    public ProcessContext(ProcessContext context, boolean isNewScope) {
        this.processName = context.processName;
        this.stateRecordName = context.stateRecordName;
        this.fieldNames = context.fieldNames;

        if (!isNewScope) {
            this.stateVarNum = context.stateVarNum;
            this.messageVarNum = context.messageVarNum;
        }
        setCurrentStateVarName();
        setCurrentMessageVarNum();
    }

    /**
     * Adds a new temporary variable to the context and returns its name in Erlang.
     * @param pcalName the name of the temporary variable in PlusCal
     * @return the name of the temporary variable in Erlang
     * @throws PcalErlangGenException if the temporary variable already exists in the current scope
     */
    public String addTemporaryVar(String pcalName) throws PcalErlangGenException {
        if (temporaryVarNames.containsKey(pcalName)) {
            throw new PcalErlangGenException("Temporary var-name " + pcalName + " is already in scope!");
        }

        int temporaryVarCount = temporaryVarsHistory.getOrDefault(pcalName, 0) + 1;
        String tempVarName = createTemporaryVarName(pcalName, temporaryVarCount - 1); // make name 0-based
        if (fieldNames.containsKey(tempVarName)) {
            throw new PcalErlangGenException(
                    "Cannot add temporary variable because there already exists a process-local variable with name "
                            + tempVarName
            );
        }
        temporaryVarNames.put(pcalName, tempVarName);
        temporaryVarsHistory.put(pcalName, temporaryVarCount);

        return tempVarName;
    }

    private static String createTemporaryVarName(String pcalName, int temporaryVarNum) {
        return String.format(TEMP_VAR_NAMES, pcalName, temporaryVarNum);
    }

    public void removeTemporaryVar(String pcalName) throws PcalErlangGenException {
        if (!temporaryVarNames.containsKey(pcalName)) {
            throw new PcalErlangGenException("Temporary var-name has already been removed!");
        } else {
            temporaryVarNames.remove(pcalName);
        }
    }

    public String getStateRecordName() {
        return stateRecordName;
    }

    /**
     * Returns the variable access for the given PlusCal variable name.
     * @param pcalVarName The variable name in PlusCal.
     * @return The variable access string of the given variable name.
     */
    private String getVarAccess(String pcalVarName) {
        return formatVarAccess(getFieldName(pcalVarName));
    }

    public String getFieldName(String pcalName) {
        return fieldNames.get(pcalName);
    }

    protected String formatVarAccess(String varStr) {
        if (isInVarDeclScope) {
            return varStr;
        }
        return String.format(PROCESS_FIELD_ACCESS, currentStateVarName, stateRecordName, varStr);
    }

    /**
     * Gets the variable name given a PlusCal variable name. The name can either be a state variable, a record key name
     *  or a temporary variable (i.e. a variable not part of the state record).
     * @param pcalVarName The variable name in PlusCal.
     * @return The variable name string.
     */
    public String getErlangVarStr(String pcalVarName) throws PcalErlangGenException {
        String var;
        if (temporaryVarNames.containsKey(pcalVarName)) {
            return temporaryVarNames.get(pcalVarName);
        } else if (fieldNames.containsKey(pcalVarName)) {
            return getVarAccess(pcalVarName);
        } else {
            if (isInRecordScope()) {
                /*
                    If we don't find the identifier and we are in a record scope, then we assume it is a record key.
                    Disadvantage: if a PlusCal program addresses a key, which has the same identifier as
                     a normal variable, then this function will wrongly return the variable name.
                 */
                // todo: add PcalErlangRecordKeyVar-s in context so that they can be looked up
                return createRecordKeyName(pcalVarName);
            } else {
                throw new PcalErlangGenException("Encountered unknown variable " + pcalVarName);
            }
        }
    }

    public static String createRecordKeyName(String pcalVarName) {
        return PREFIX_RECORD_KEY + pcalVarName;
    }

    public String getProcNumberFieldAccess() {
        return formatVarAccess(getProcNumberFieldStr());
    }

    public String getProcNumberFieldStr() {
        return PREFIX_INTERNAL_PROC_VAR + "Num";
    }

    public String getCurrentStateVarName() {
        return currentStateVarName;
    }

    public String getCurrentMessageVarName() {
        return currentMessageVarName;
    }

    /**
     * Gets the name of the process
     * @return The name of the process
     */
    public String getProcessName() {
        return processName;
    }

    /**
     * Generates the next state variable name, returns it and sets it internally into the context.
     * @return The next variable name
     */
    public String nextStateVarName() {
        stateVarNum++;
        setCurrentStateVarName();
        return currentStateVarName;
    }

    public String nextMessageVarName() {
        messageVarNum++;
        setCurrentMessageVarNum();
        return currentMessageVarName;
    }

    private void setCurrentStateVarName() {
        currentStateVarName = String.format(PROCESS_STATE_VAR_NAMES, stateVarNum);
    }

    private void setCurrentMessageVarNum() {
        currentMessageVarName = String.format(MESSAGE_VAR_NAMES, messageVarNum);
    }

    private void fillFieldNames(Vector fieldVarDecls) {
        for (Object varDeclObj : fieldVarDecls) {
            AST.VarDecl varDecl = (AST.VarDecl) varDeclObj;
            String pcalName = varDecl.var;

            fieldNames.put(pcalName, createVarName(pcalName));
        }
    }

    private static String createVarName(String pcalVarName) {
        return PREFIX_VAR + pcalVarName;
    }

    public String changeStateVarName(int stateVarNum) {
        this.stateVarNum = stateVarNum;
        setCurrentStateVarName();
        return currentStateVarName;
    }

    public int getStateVarNum() {
        return stateVarNum;
    }

    public String getAndIncrementWhileFunc(){
        String result = PREFIX_FUNCTION_WHILE + whileNum;
        whileNum++;
        return result;
    }

    public void startRecordScope() {
        recordScopeDepth++;
    }
    public void endRecordScope() {
        if (isInRecordScope()) {
            recordScopeDepth--;
        }
    }
    public boolean isInRecordScope() {
        return recordScopeDepth > 0;
    }

    /**
     * Begins a variable declaration scope.
     * Use this before parsing variable declarations.
     */
    public void beginVarDeclScope() {
        isInVarDeclScope = true;
    }

    /**
     * Ends a variable declaration scope.
     * Use this after the parsing of variable declarations has finished.
     */
    public void endVarDeclScope() {
        isInVarDeclScope = false;
    }

}
