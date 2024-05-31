package pcal;

import pcal.exception.PcalErlangGenException;
import java.util.*;
import static pcal.PCalErlangConstants.*;
import static pcal.PcalErlangGenUtil.*;
import static pcal.TLAToken.IDENT;

/**
 * Converts TLAExpr's to equivalent Erlang strings.
 */
public class TLAExprToErlangStrConverter {
    /**
     * A mapping of PlusCal operator strings to Erlang operator strings.
     * The precedences are taken from <a href="https://lamport.azurewebsites.net/tla/summary-standalone.pdf">this website</a>
     * and are calculated with 17 - Precedence,
     * as our priority is calculated opposite of Pluscal's.
     */
    private final Map<String, MapValueTuple> operatorMapping;

    public TLAExprToErlangStrConverter() {
        // todo: maybe sort symbols (by priority or by use) (low prio)
        // todo: declare pluscal symbols in some central file (low prio)
        this.operatorMapping = Map.ofEntries(
                Map.entry("%", new MapValueTuple("%s rem %s", 7, false)),
//                Map.entry("/\\", new MapValueTuple("%s and %s", 14, false)),
                Map.entry("/\\", new MapValueTuple("%s andalso %s", 14, false)), // short circuit
//                Map.entry("\\/", new MapValueTuple("%s or %s", 14, false)),
                Map.entry("\\/", new MapValueTuple("%s orelse %s", 14, false)), // short circuit
                Map.entry("~", new MapValueTuple("not %s", 13, false)),
                Map.entry("<=>", new MapValueTuple("%s =:= %s", 15, false)),
                Map.entry("=>", new MapValueTuple("(not %s) or %s", 15, false)),
                Map.entry(">=", new MapValueTuple("%s >= %s", 12, false)),
                // for \leq both character orders are possible
                Map.entry("<=", new MapValueTuple("%s =< %s", 12, false)),
                Map.entry("=<", new MapValueTuple("%s =< %s", 12, false)),
                Map.entry("<", new MapValueTuple("%s < %s", 12, false)),
                Map.entry(">", new MapValueTuple("%s > %s", 12, false)),
                Map.entry("=", new MapValueTuple("%s =:= %s", 12, false)),
                Map.entry("#", new MapValueTuple("%s =/= %s", 12, false)),
                Map.entry("/=", new MapValueTuple("%s =/= %s", 12, false)),
                Map.entry("\\div", new MapValueTuple("%s div %s", 4, false)), // integer division
                Map.entry("+", new MapValueTuple("%s + %s", 7, false)),
                Map.entry("-", new MapValueTuple("%s - %s", 6, false)),
                Map.entry("*", new MapValueTuple("%s * %s", 4, false)),
                Map.entry("\\o", new MapValueTuple("%s ++ %s", 6, false)),
                Map.entry("^", new MapValueTuple("math:pow(%s, %s)", 3, false)),
                Map.entry("..", new MapValueTuple("sets:from_list(lists:seq(%s, %s))", 8, false)),
                Map.entry("\\subseteq", new MapValueTuple("sets:is_subset(%s, %s ", 12, false)),
                Map.entry("\\cap", new MapValueTuple("sets:intersection(%s, %s)", 9, false)),
                Map.entry("\\cup", new MapValueTuple("sets:union(%s, %s)", 9, false)),
                Map.entry("\\union", new MapValueTuple("sets:union(%s, %s)", 9, false)),
                Map.entry("\\", new MapValueTuple("sets:subtract(%s, %s)", 9, false)),
                Map.entry("\\in", new MapValueTuple("sets:is_element(%s, %s)", 12, false)),
                Map.entry("UNION", new MapValueTuple("sets:union( sets:to_list(%s))", 9, false)),
                Map.entry("SUBSET", new MapValueTuple(ERLA_LIBS_MODULE_SETS_NAME + ":powerSet(%s)", 9, false)),
                Map.entry(".", new MapValueTuple("maps:get(%s, %s)", 1, false)), // record field access
                Map.entry("@@", new MapValueTuple("maps:merge(%s, %s)", 11, false)), // record merge
                Map.entry("Append", new MapValueTuple("%s ++ [%s]", 0, true)), // todo: check prio value
                Map.entry("Head", new MapValueTuple("hd(%s)", 0, true)), // todo: check prio value
                Map.entry("Tail", new MapValueTuple("tl(%s)", 0, true)), // todo: check prio value
                Map.entry("Len", new MapValueTuple("length(%s)", 3, true)), // todo: check prio value
                Map.entry("SubSeq", new MapValueTuple("lists:sublist(%s, %s, %s)", 0, true)),
                Map.entry("ToString", new MapValueTuple("integer_to_list(%s)", 0, true)), // todo: check prio value
                Map.entry("\\inFunction", new MapValueTuple("%s===%s", 12, false)),
                Map.entry("Cardinality", new MapValueTuple("sets:size(%s)", 0, true))
        );
    }

    public String TLAExprToErlangStr(TLAExpr expr, ErlangProcessContext context) throws PcalErlangGenException {
        return TLAExprToErlangStrInternal(TLAExprToList(expr), context);
    }

    private String TLAExprToErlangStrInternal(List<TLAToken> tokens, ErlangProcessContext context) throws PcalErlangGenException {
        if (tokens.isEmpty()) {
            return "";
        }

        int firstOpPos = findHighestPriorityBinaryOperator(tokens);
        if (firstOpPos < 0) {

            /*
              Handle parenthesized expressions
             */
            if ((tokens.get(0)).string.equals("(") && (tokens.get(tokens.size() - 1)).string.equals(")")) {
                tokens.remove(0);
                tokens.remove(tokens.size() - 1);
                return "(" + TLAExprToErlangStrInternal(tokens, context) + ")";
            }

            /*
              Handle Non-binary expression
             */
            TLAToken firstToken = tokens.get(0);
            switch (firstToken.string) {
                case "{":
                    /*
                      Normal Set declaration
                     */
                    return setGen(tokens, context);
                case "<<":
                    /*
                      Sequence/Tuple declaration
                     */
                    return sequenceGen(tokens, context);
                case "[":
                    return recordGen(tokens, context);
            }

            int tokenType = firstToken.type;
            String currTokenStr = firstToken.string;
            if (tokenType == TLAToken.STRING) {
                currTokenStr = "\"" + currTokenStr + "\"";
            } else if (tokenType == IDENT) {
                /*
                  Identifiers are for now only variables and record keys.
                 */
                String pcalVarName = currTokenStr;
                currTokenStr = context.getErlangVarStr(pcalVarName);
                if (tokens.size() > 1 && tokens.get(1).string.equals("[")) {
                    return genAccess(tokens, context);
                }
            } else if (tokenType == TLAToken.BUILTIN) {
                if (currTokenStr.equals("TRUE")) {
                    currTokenStr = "true";
                } else if (currTokenStr.equals("FALSE")) {
                    currTokenStr = "false";
                }
            }
            return currTokenStr;
        } else if (isUnaryOperator(tokens.get(firstOpPos))) {
            /*
              Handle unary expressions
              such as not,UNION and SUBSET
             */
            TLAToken binaryOpToken = tokens.get(firstOpPos);
            String binaryOpErlangStr = operatorMapping.get(binaryOpToken.string).string;
            List<TLAToken> right = tokens.subList(firstOpPos + 1, tokens.size());

            String rightStr = TLAExprToErlangStrInternal(right, context);
            return String.format(binaryOpErlangStr, rightStr);
        } else {
            /*
              Handle binary operations and functions
             */

            TLAToken binaryOpToken = tokens.get(firstOpPos);
            MapValueTuple mapTuple = operatorMapping.get(binaryOpToken.string);
            String binaryOpErlangStr = mapTuple.string;
            if (mapTuple.isUnary) {
                /*
                  Parse PlusCal functions
                 */
                return parseFunctionOp(binaryOpErlangStr, tokens, firstOpPos, context);
            } else {
                /*
                  Parse binary operation
                 */
                List<TLAToken> left = new ArrayList<>(tokens.subList(0, firstOpPos));
                List<TLAToken> right = new ArrayList<>(tokens.subList(firstOpPos + 1, tokens.size()));

                // exception: record access
                if (binaryOpToken.string.equals(".")) {
                    return parseRecordAccess(left, right, binaryOpErlangStr, context);
                }

                String leftStr = TLAExprToErlangStrInternal(left, context);
                String rightStr = TLAExprToErlangStrInternal(right, context);

                if (binaryOpToken.string.equals("@@")) { // todo: figure out a way to handle this more cleverly
                    String temp = leftStr;
                    leftStr = rightStr;
                    rightStr = temp;
                }

                return "(" + String.format(binaryOpErlangStr, leftStr, rightStr) + ")";
            }
        }
    }

    public String parseAssignment(AST.Lhs lhs, TLAExpr rhs, ErlangProcessContext context) throws PcalErlangGenException {
        boolean isMemberAssignment = !lhs.sub.tokens.isEmpty();
        String pcalFieldName = lhs.var;
        String erlangFieldName = context.getFieldName(pcalFieldName);
        String right = TLAExprToErlangStr(rhs, context);
        if (isMemberAssignment) {
            /*
                Member assignment
             */
            Vector leftTokens = (Vector) lhs.sub.tokens.get(0);
            if (leftTokens == null) {
                throw new PcalErlangGenException("Left-hand side tokens are null", lhs);
            }
            /*
                Per PlusCal grammar, the left-hand side of an assignment always begins with an identifier.
                (Source: https://lamport.azurewebsites.net/pubs/pluscal.pdf)
            */
            String erlangName = context.getErlangVarStr(pcalFieldName); // parse ID
            String keys = parseKeysToCommaSeparatedList(leftTokens, context);
            // todo: update var type of assigned member
            right = String.format(RECORD_ACCESS_ASSIGNMENT, erlangName, keys, right);
        }

        return formatVarAssignment(erlangFieldName, right, context);
    }

    /**
     * Parses a definition and returns a tuple {name, value}, where "name" is the name of the definition in PlusCal and
     *  "value" is the definition's value parsed in Erlang.
     * @param def The definition to be parsed.
     * @param context The current context.
     * @return A tuple {name, value}, where "name" is the name of the definition in PlusCal and
     *  "value" is the definition's value parsed in Erlang.
     */
    public Map.Entry<String, String> parseDefinition(Vector<TLAToken> def, ErlangDefinitionContext context) throws PcalErlangGenException {
        // todo: provide context so that previously defined definitions can be used in other definition declarations
        if (def.size() < 3) {
            throw new PcalErlangGenException("Cannot parse definition \"" + def + "\". Invalid length." );
        }
        String pcalDefName = def.get(0).string;
        if (!def.get(1).string.equals("==")) {
            throw new PcalErlangGenException("Cannot parse definition \"" + def
                    + "\". Expected second token to be \"==\", but was " + def.get(1).string
            );
        }

        String value = this.TLAExprToErlangStrInternal(new ArrayList<>(def.subList(2, def.size())), context);

        context.addDefinition(pcalDefName);

        return Map.entry(pcalDefName, value);
    }

    /******************************************************************************************************************/

    private String parseRecordAccess(List<TLAToken> left, List<TLAToken> right, String binaryOpErlangStr, ErlangProcessContext context) throws PcalErlangGenException {
        String leftStr = TLAExprToErlangStrInternal(left, context);

        String recordKey = ErlangProcessContext.createRecordKeyName(right.get(0).string); // todo: parse right properly, not only first ID

        return String.format(binaryOpErlangStr, recordKey, leftStr);
    }

    private String genAccess(List<TLAToken> tokens, ErlangProcessContext context) throws PcalErlangGenException {
        String erlangVar = context.getErlangVarStr(tokens.get(0).string);
        String keys = parseKeysToCommaSeparatedList(tokens, context);
        return String.format(RECORD_ACCESS_STATEMENT, erlangVar, keys);
    }

    /**
     * Parses a possibly multidimensional member-access and produces a
     * comma-separated string representation of the keys.
     *
     * @param tokens  the list of tokens, representing the member-access expression
     * @param context the process' context
     * @return a comma-separated string, containing the parsed key expressions
     */
    private String parseKeysToCommaSeparatedList(List<TLAToken> tokens, ErlangProcessContext context) throws PcalErlangGenException {
        List<List<TLAToken>> keysAsList = getKeysAsList(tokens);
        List<String> result = new ArrayList<>();
        // todo: add keys to record scope to fix the behavior of keys being overridden by variables of the same name
        context.startRecordScope();
        for (List<TLAToken> key : keysAsList) {
            String parsedArgument = TLAExprToErlangStrInternal(key, context);
            result.add(parsedArgument);
        }
        context.endRecordScope();

        return String.join(", ", result);
    }

    private String parseFunctionOp(String binaryOpErlangStr, List<TLAToken> tokens, int firstOpPos, ErlangProcessContext context) throws PcalErlangGenException {
        // remove function identifier, "(" and ")"
        tokens.remove(firstOpPos);
        tokens.remove(firstOpPos);
        tokens.remove(tokens.size() - 1);
        // parse arguments
        String[] parameterArr = parseArguments(tokens, context);
        // format result
        if (binaryOpErlangStr.equals("lists:sublist(%s, %s, %s - %s + 1)")) {
            // A = <<1,2,3,4,5>>; SubSeq(A, 2, 3) <- <<3,4>>
            // lists:sublist(A, 2, (3 - 2) + 1)
            return String.format(binaryOpErlangStr, parameterArr[0], parameterArr[1],
                    parameterArr[2], parameterArr[1]);
        }
        return String.format(binaryOpErlangStr, (Object[]) parameterArr);
    }

    private String setGen(List<TLAToken> tokens, ErlangProcessContext context) throws PcalErlangGenException {
        // remove "{}"
        tokens.remove(0);
        tokens.remove(tokens.size() - 1);

        int filterOrMappingSeparatorPos = new PCalTokenIterator(tokens).getNextPosForStrInScope(":");
        if (!(filterOrMappingSeparatorPos == -1)) {
            /*
                Parse filter expression
             */
            List<TLAToken> left = new ArrayList<>(tokens.subList(0, filterOrMappingSeparatorPos));
            List<TLAToken> right = new ArrayList<>(tokens.subList(filterOrMappingSeparatorPos + 1, tokens.size()));
            return GenFilterSetExpr(left, right, context);
        }

        // parse arguments
        String[] parameters = parseArguments(tokens, context);
        String result = "sets:from_list(";
        int op = findHighestPriorityBinaryOperator(tokens);
        if (op == -1) {
            result += "[" + String.join(", ", parameters) + "])";
        } else if (tokens.get(op).string.equals("..")) {
            result += String.join(", ", parameters) + ")";
        } else {
            result += "[" + String.join(", ", parameters) + "])";
        }
        // return result
        return result;
    }

    private String GenFilterSetExpr(List<TLAToken> left, List<TLAToken> right, ErlangProcessContext context) throws PcalErlangGenException {
        /*
            For now, we only support expressions of the following type:
                {x \in Xs : P(x)}, where P(x) is a predicate (specifically a boolean TLA expression) and Xs is a set.
         */

        if (left.get(0).type != IDENT || !left.get(1).string.equals("\\in")) {
            throw new PcalErlangGenException("Cannot parse complex set-filter expressions");
        }
        // get temporary variable name and add to context
        String pcalElementName = left.get(0).string;
        String tempVarName = context.addTemporaryVar(pcalElementName);

        // get name of set
        String set = TLAExprToErlangStrInternal(new ArrayList<>(left.subList(2, left.size())), context);

        // parse predicate
        String parsedFilterExpr = TLAExprToErlangStrInternal(right, context);

        // remove temporary variable from context
        context.removeTemporaryVar(pcalElementName);

        // format result
        return String.format(SET_FILTER, tempVarName, parsedFilterExpr, set);
    }

    private String sequenceGen(List<TLAToken> tokens, ErlangProcessContext context) throws PcalErlangGenException {
        // remove "<<>>"
        tokens.remove(0);
        tokens.remove(tokens.size() - 1);
        // parse arguments
        String[] parameters = parseArguments(tokens, context);
        // return result
        return "[" + String.join(", ", parameters) + "]";
    }

    private String recordGen(List<TLAToken> tokens, ErlangProcessContext context) throws PcalErlangGenException {
        // remove "[", "]"
        tokens.remove(0);
        tokens.remove(tokens.size() - 1);
        // parse arguments
        ArrayList<String> arguments = parseRecordArguments(tokens, context);
        // format map
        String argStr = String.join(", ", arguments);
        for (TLAToken token : tokens) {
            if (token.string.contains("\\in")) {
                return argStr; // workaround, todo: fix this
            }
        }
        return String.format("#{%s}", argStr);
    }

    private ArrayList<String> parseRecordArguments(List<TLAToken> tokens, ErlangProcessContext context) throws PcalErlangGenException {
        ArrayList<String> keyValueStrings = new ArrayList<>();

        PCalTokenIterator iterator = new PCalTokenIterator(tokens);
        int nextCommaPos;
        int prevCommaPos = -1;
        do {
            nextCommaPos = findNextCommaPos(iterator);

            boolean isLastPair = nextCommaPos == -1;
            // set end of pair position
            int pairEndIndex;
            if (isLastPair) {
                pairEndIndex = tokens.size();
            } else {
                pairEndIndex = nextCommaPos;
            }

            // parse key-value pair
            List<TLAToken> keyValueTokens = new ArrayList<>(tokens.subList(prevCommaPos + 1, pairEndIndex));
            String keyValueString = parseKeyValuePair(keyValueTokens, context);

            // add key-value pair to list
            keyValueStrings.add(keyValueString);

            prevCommaPos = nextCommaPos;

        } while (nextCommaPos != -1);

        return keyValueStrings;
    }

    private String parseKeyValuePair(List<TLAToken> tokens, ErlangProcessContext context) throws PcalErlangGenException {
        String key = "";
        PCalTokenIterator iterator = new PCalTokenIterator(tokens);
        int keyValueSeparatorPos = iterator.getNextPosForStrInScope("|->");
        boolean isSetKey = false;
        if (keyValueSeparatorPos < 0) {
            throw new PcalErlangGenException("No record separator found in record assignment");
        } else if (keyValueSeparatorPos > 1) {
            // complex key expression
            iterator.reset();
            int inPos = iterator.getNextPosForStrInScope("\\in");
            if (inPos < 0) {
                throw new PcalErlangGenException("Cannot parse complex key expression in record generation");
            } else {
                // record is of the form "[i \in S |-> ...];"
                List<TLAToken> setTokens = new ArrayList<>(tokens.subList(inPos + 1, keyValueSeparatorPos));
                key = TLAExprToErlangStrInternal(setTokens, context);
                isSetKey = true;
            }
        }

        // parse value
        List<TLAToken> valTokens = new ArrayList<>(tokens.subList(keyValueSeparatorPos + 1, tokens.size()));
        String val = TLAExprToErlangStrInternal(valTokens, context);

        // return result
        if (!isSetKey) {
            key = ErlangProcessContext.createRecordKeyName(tokens.get(0).string); // format erlang key string
            return String.format("%s => %s", key, val);
        } else {
            return String.format("maps:from_list([{Key, %s} || Key <- sets:to_list(%s)])", val, key);
        }
    }

    /**
     * Parses a comma-separated token-list.
     *
     * @param tokens  The comma-separated list of tokens to be parsed.
     * @param context The process context.
     * @return An array of type Object, containing the parsed argument strings.
     */
    private String[] parseArguments(List<TLAToken> tokens, ErlangProcessContext context) throws PcalErlangGenException {
        // calculate the maximum number of arguments
        int maxNumberOfArguments = (int) Math.floor((double) (tokens.size() + 1) / 2);

        // create array
        String[] argumentArr = new String[maxNumberOfArguments];

        if (maxNumberOfArguments == 0) {
            return argumentArr;
        }

        // fill array
        int lastCommaPos = -1;
        int numberOfArgs = 0;
        PCalTokenIterator iterator = new PCalTokenIterator(tokens);
        for (int i = 0; i <= argumentArr.length - 1; i++) {
            int nextCommaPos = findNextCommaPos(iterator);

            boolean isLastArgument = nextCommaPos == -1;
            // set end of argument position
            int argumentEndIndex;
            if (isLastArgument) {
                argumentEndIndex = tokens.size();
            } else {
                argumentEndIndex = nextCommaPos;
            }

            // parse argument
            List<TLAToken> argument = new ArrayList<>(tokens.subList(lastCommaPos + 1, argumentEndIndex));
            String argumentStr = TLAExprToErlangStrInternal(argument, context);

            // add to array of arguments
            argumentArr[i] = argumentStr;
            numberOfArgs++;

            // break if no more commas were found and the last argument has been processed
            if (isLastArgument) {
                break;
            }
            lastCommaPos = nextCommaPos;
        }

        return Arrays.copyOf(argumentArr, numberOfArgs);
    }

    /********************************************************************************************************************/

    private int findNextCommaPos(PCalTokenIterator iterator) {
        TLAToken currentToken = iterator.nextTokenInScope();
        while (currentToken != null) {
            if (currentToken.string.equals(",")) {
                return iterator.getCurrentPos();
            }
            currentToken = iterator.nextTokenInScope();
        }
        return -1;
    }

    /**
     * Parses a single token.
     *
     * @param token   The token to be parsed.
     * @param context The process context.
     * @return The translated token as an erlang string.
     */
    private String parseSingleToken(TLAToken token, ErlangProcessContext context) throws PcalErlangGenException {
        // build list with single token
        ArrayList<TLAToken> singleTokenList = new ArrayList<>();
        singleTokenList.add(token);
        // parse token
        return TLAExprToErlangStrInternal(singleTokenList, context);
    }

    /**
     * Searches for the binary operator with the highest priority in the list and returns its index.
     *
     * @param tokens The list of tokens to be searched in.
     * @return The index of the  binary operator with the highest priority.
     */
    private int findHighestPriorityBinaryOperator(List<TLAToken> tokens) {
        int indexOfHighestPriority = -1;
        int highestPriority = -1;

        PCalTokenIterator iterator = new PCalTokenIterator(tokens);
        TLAToken currentToken = iterator.nextTokenInScope();
        while (currentToken != null) {
            if (currentToken.type == TLAToken.BUILTIN || currentToken.type == IDENT) {
                boolean isOpInMap = operatorMapping.containsKey(currentToken.string);
                if (isOpInMap) {
                    if (operatorMapping.get(currentToken.string).priority > highestPriority) {
                        indexOfHighestPriority = iterator.getCurrentPos();
                        highestPriority = operatorMapping.get(currentToken.string).priority;
                    }
                }
            }

            currentToken = iterator.nextTokenInScope();
        }
        return indexOfHighestPriority;
    }

    /**
     * Receives a possibly multidimensional member access expression as a list of tokens
     * and returns a list of the arguments, e.g.
     * input: "a[0][2]"
     * output: listOf(0, 2).
     *
     * @param tokens the member access expression, from which the arguments are to be returned
     * @return the list of arguments, contained in the input expression
     */
    private List<List<TLAToken>> getKeysAsList(List<TLAToken> tokens) {
        List<TLAToken> workingList = tokens;
        if (tokens.get(0).type == IDENT) {
            // remove identifier from working list
            workingList = new ArrayList<>(workingList.subList(1, workingList.size()));
        }

        ArrayList<List<TLAToken>> result = new ArrayList<>();
        PCalTokenIterator iterator = new PCalTokenIterator(workingList);
        TLAToken token = iterator.nextToken();
        int bracketCount = 0;
        int openingPos = -1;
        int closingPos;
        while (token != null) {
            if (token.string.equals("[")) {
                openingPos = iterator.getCurrentPos();
                bracketCount++;
            } else if (token.string.equals("]")) {
                bracketCount--;
                if (bracketCount == 0) {
                    closingPos = iterator.getCurrentPos();
                    // found end of argument scope => add argument to list
                    result.add(new ArrayList<>(workingList.subList(openingPos + 1, closingPos)));
                }
            }

            token = iterator.nextToken();
        }

        return result;
    }

    private boolean isUnaryOperator(TLAToken tlaToken) {
        // todo: remove because superfluous. Set each of the following operators' isFunction flag to true
        switch (tlaToken.string) {
            case "~":
                //case "Cardinality":
            case "SUBSET":
            case "UNION":
                return true;
            default:
                return false;
        }
    }
}