package pcal;

import pcal.exception.PcalErlangGenException;

import static pcal.PCalErlangConstants.*;

public class ErlangStateField {
    public enum FieldType {
        PROCESS_LOCAL_VARIABLE,
        CONSTANT,
        INTERNAL_VAR
        ;

        public String createFieldNameForType(String pcalName) throws PcalErlangGenException {
            switch (this) {
                case PROCESS_LOCAL_VARIABLE: return PREFIX_VAR + pcalName;
                case CONSTANT: return PREFIX_CONSTANT_VAR + pcalName;
                case INTERNAL_VAR: return PREFIX_INTERNAL_PROC_VAR + pcalName;
                default: throw new PcalErlangGenException("Cannot create field name for unknown field type " + this);
            }
        }
    }

    private final FieldType type;

    private final String name;

    public ErlangStateField(String pcalName, FieldType type) throws PcalErlangGenException {
        this.type = type;
        this.name = type.createFieldNameForType(pcalName);
    }

    public FieldType getType() {
        return type;
    }

    public String getName() {
        return name;
    }
}
