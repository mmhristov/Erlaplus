package org.erla;

import pcal.PcalBuiltInSymbols;
import pcal.PcalErlangGenUtil;
import pcal.TLAExprToErlangStrConverter;
import pcal.exception.PcalErlangGenException;
import pcal.exception.TokenizerException;

public class Util {
    public record MsgPair(String x, String y) {
        private static TLAExprToErlangStrConverter exprConv;
        @Override
        public String toString() {
            if (exprConv == null) {
                exprConv = new TLAExprToErlangStrConverter();
                PcalBuiltInSymbols.Initialize();
            }
            try {
                return "{"
                        + x + ", "
                        + exprConv.TLAExprToErlangStr(PcalErlangGenUtil.tokenizeTlaExpr(y), null)
                        + "}";
            } catch (TokenizerException | PcalErlangGenException e) {
                throw new RuntimeException("Error in constructing the message \"" + y + "\" as string: " + e);
            }
        }
    }
}
