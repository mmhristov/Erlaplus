package pcal;

public final class PCalErlangConstants {
    private PCalErlangConstants() {
        // hide constructor, since it should not be instantiated
    }

    // todo: extract strings from PCalErlangGen to here (low priority)
    // todo: make placeholders in template strings more readable by using e.g.
    //  StringSubstitutor From Apache Commons Text.

    public static String ERLA_LIBS_MODULE_COMMUNICATION_NAME = "erla_libs_comm";
    public static String ERLA_LIBS_MODULE_SETS_NAME = "erla_libs_sets";
    public static String ERLA_LIBS_MODULE_UTIL_NAME = "erla_libs_util";

    public static String GLOBAL_QUEUES_NAME = "queues";

    public static int NUM_SPACES_FOR_INDENT = 4;

    public static String MODULE_DECL = "-module(%s)";
    public static String EXPORT_DECL = "-export[]";

    public static String PREFIX_PROCESS_START_FUNC = "start_";
    public static String PREFIX_PROCESS_STATE_NAME = "state_";
    public static String PREFIX_VAR = "var_";
    public static String PREFIX_INTERNAL_PROC_VAR = "procvar_";
    public static String PREFIX_RECORD_KEY = "key_";
    public static String PREFIX_FUNCTION_WHILE = "function_while";
    public static String PREFIX_PROCESS = "process_";

    public static String PROCESS_STATE_VAR_NAMES = "State%o";
    public static String MESSAGE_VAR_NAMES = "Message%o";
    public static String TEMP_VAR_NAMES = "Temp_%s%o";


    /** A template string for accessing a record's field.
     *  Template: Var#record.field.
     */
    public static String PROCESS_FIELD_ACCESS = "%s#%s.%s";
    /**
     * A template string for variable assignment.
     *  Template: NewVar = OldVar#record{field = value}
     */
    public static String PROCESS_VAR_ASSIGNMENT = "%s = %s#%s{%s = %s}";
    public static String TEMP_VAR_ASSIGNMENT= "%s = %s";
    public static char COMMENT_CHAR = '%';

    public static String SINGLE_LINE_COMMENT = Character.toString(COMMENT_CHAR) + Character.toString(COMMENT_CHAR) + " %s"; // escape % char for formatting

    public static String PRINT_STATEMENT =  "erlang:display(%s)";
    public static String SEND_STATEMENT = ERLA_LIBS_MODULE_COMMUNICATION_NAME + ":send(%s, %s)"; // erla_libs:send(receiver, message)
    public static String BROADCAST_STATEMENT = ERLA_LIBS_MODULE_COMMUNICATION_NAME + ":broadcast(%s)"; // erla_libs:broadcast(message)
    public static String REGISTER_STATEMENT = ERLA_LIBS_MODULE_COMMUNICATION_NAME + ":register_proc(%s)";
    public static String GET_ALL_PROCS_STATEMENT = ERLA_LIBS_MODULE_COMMUNICATION_NAME + ":get_all_procs()";
    public static String INITIAL_FUNCTION_DECL = "maps:from_list(lists:map(%s, %s))";
    public static String RECORD_ACCESS_STATEMENT = ERLA_LIBS_MODULE_UTIL_NAME + ":get_nested_value(%s, [%s])";
    public static String RECORD_ACCESS_ASSIGNMENT = ERLA_LIBS_MODULE_UTIL_NAME + ":update_nested_value(%s, [%s], %s)";
    public static String SET_FILTER = "sets:filter(fun(%s) -> %s end, %s)";

    /**
     * Send operation types.
     */
    public enum SendType {
        SEND,
        BROADCAST;

        @Override
        public String toString() {
            String result = "";
            switch (this) {
                case SEND: result = "send"; break;
                case BROADCAST: result = "broadcast"; break;
                default: result = this.name();
            }
            return result;
        }
    }

}
