package pcal;

import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import static pcal.PCalErlangConstants.PROCESS_VAR_ASSIGNMENT;

public class PcalErlangGenUtil {

    public static List<TLAToken> TLAExprToList(TLAExpr expr) {
        ArrayList<TLAToken> exprList = new ArrayList<>();
        for (int i = 0; i < expr.tokens.size(); i++) {
            exprList.addAll(new ArrayList<>((Vector) expr.tokens.get(i)));
        }
        return exprList;
    }

    public static String formatVarAssignment(String left, String right, ProcessContext context) {
        String prevStateVarName = context.getCurrentStateVarName();
        String currStateVarName = context.nextStateVarName();
        String stateRecName = context.getStateRecordName();

        return String.format(
                PROCESS_VAR_ASSIGNMENT,
                currStateVarName, prevStateVarName,
                stateRecName, left,
                right
        ) + ",";
    }

}
