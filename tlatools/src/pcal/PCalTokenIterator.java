package pcal;

import pcal.exception.PcalErlangGenException;

import java.util.List;
import java.util.Map;

public class PCalTokenIterator {
    private static final int INIT_POS = -1;
    private static final String sEmpty = "";

    private int currentPos = INIT_POS;
    private final List<TLAToken> tokens;
    private final Map<String, String> scopeOpeningDelimiters;

    public PCalTokenIterator(List<TLAToken> tokens) {
        this.tokens = tokens;
        this.scopeOpeningDelimiters = Map.ofEntries(
                Map.entry("(", ")"),
                Map.entry("{", "}"),
                Map.entry("<<", ">>"),
                Map.entry("[", "]")
        );
    }

    public int getCurrentPos() {
        return currentPos;
    }


    public TLAToken nextToken() {
        TLAToken res = null;
        currentPos++;
        if (currentPos <= tokens.size() - 1) {
            res = tokens.get(currentPos);
        }

        return res;
    }

    /**
     * Iterates until it finds the next token in scope.
     * @return The next token in scope.
     */
    public TLAToken nextTokenInScope() {
        currentPos++;
        String openingBracket = sEmpty;
        String closingBracket = sEmpty;
        int openScopeCount = 0;
        for (int i = currentPos; i <= tokens.size() - 1; i++) {
            TLAToken token = tokens.get(i);

            if (openScopeCount < 0) {
                return null;
            }

            if (openScopeCount == 0) {
                if (scopeOpeningDelimiters.containsKey(token.string)) {
                    openingBracket = token.string;
                    closingBracket = scopeOpeningDelimiters.get(token.string);
                    openScopeCount++;
                } else {
                    currentPos = i;
                    return token;
                }
            } else {
                if (token.string.equals(closingBracket)) {
                    openScopeCount--;
                } else if (openingBracket.equals(token.string)) {
                    openScopeCount++;
                }
            }
        }
        return null;
    }

    /**
     * Returns the next position of the element IN SCOPE that matches the parameter string if found, and -1 if not.
     *  Use "getNextPosForStr" if scoping should not be used.
     *
     * @param symbol the string representation of the element that is to be found
     * @return the next position of the element that matches the parameter string if found, and -1 if not.
     */
    public int getNextPosForStrInScope(String symbol) {
        TLAToken currentToken = this.nextTokenInScope();
        int tokenPos = -1;
        while (currentToken != null) {
            if (currentToken.string.equals(symbol)) {
                tokenPos = this.getCurrentPos();
                break;
            }
            currentToken = this.nextTokenInScope();
        }

        return tokenPos;
    }

    /**
     * Returns the next position of the element that matches the parameter string if found, and -1 if not.
     *  Use "getNextPosForStrInScope" if scoping should be used.
     *
     * @param symbol the string representation of the element that is to be found
     * @return the next position of the element that matches the parameter string if found, and -1 if not.
     */
    public int getNextPosForStr(String symbol) {
        TLAToken currentToken = nextToken();
        int tokenPos = -1;
        while (currentToken != null) {
            if (currentToken.string.equals(symbol)) {
                tokenPos = this.getCurrentPos();
                break;
            }
            currentToken = nextToken();
        }

        return tokenPos;
    }

    /**
     * Resets the iterator to its starting position.
     */
    public void reset() {
        this.currentPos = INIT_POS;
    }

}
