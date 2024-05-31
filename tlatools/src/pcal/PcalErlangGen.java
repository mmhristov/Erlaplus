package pcal;

import java.io.File;
import java.util.*;

import pcal.exception.PcalErlangGenException;

import static pcal.PCalErlangConstants.*;
import static pcal.PcalErlangGenUtil.*;

public class PcalErlangGen {

    /**
     * The resulting erlang file: a vector of strings,
     * in which each element of the vector corresponds to one line
     * of the erlang program.
     */
    private final Vector<String> erlangCode = new Vector<>();

    /**
     * The current indentation level.
     */
    private int indent = 0;

    /**
     * The position of the exported functions declaration.
     */
    private int exportedFuncsPos;

    /**
     * The position of the end of the last module attribute declaration.
     *  Note: use updateEndOfModuleAttributePos() to update this variable.
     */
    private int endOfModuleAttributesPos;

    /**
     * The position of the end of the last function declared.
     */
    private int endOfFunctionPos; // todo: understand what the intention behind this was and probably use endOfModuleAttributesPos instead

    /**
     * The current position of writing
     */
    private int currentPos;

    /**
     * Converts TLAExpr's to equivalent Erlang strings.
     */
    private TLAExprToErlangStrConverter exprConverter;

    /**
     * A mapping of PlusCal constant names and Erlang constant names.
     */
    private final Map<String, String> allConstantVarNames = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);

    /**
     * Generates the Erlang translation.
     *
     * @param ast The AST produced by parsing and exploding.
     * @return The generated Erlang program as a vector of strings.
     */
    // use symbol table if you need to look up any identifier
    public PcalErlangGenResult generate(AST ast, PcalSymTab symTab) throws PcalErlangGenException {
        // init expression converter
        exprConverter = new TLAExprToErlangStrConverter();

        addInitialization();

        if (ast.getClass().equals(AST.UniprocessObj.getClass()))
            GenUniprocess((AST.Uniprocess) ast);
        else if (ast.getClass().equals(AST.MultiprocessObj.getClass()))
            GenMultiprocess((AST.Multiprocess) ast);
        else
            throw new PcalErlangGenException("Unknown root AST type: " + ast.getClass());

        // get definitions
        TLAExpr defs = ((AST.RootProcess) ast).defs;

        Map<String, String> parsedDefinitions = null;
        // parse definitions
        if (defs != null) {
            parsedDefinitions = parseDefinitions(defs);
        }

        generateConstantDeclarations(parsedDefinitions);

        if (PcalParams.GenErlangMainFunction) {
            generateMain(ast, ((AST.RootProcess) ast).getAllProcessNames(), symTab);
        }

        return new PcalErlangGenResult(erlangCode);
    }

    private void generateMain(AST ast, List<String> allProcessNames, PcalSymTab symTab) throws PcalErlangGenException {
        String initFuncName = "init";
        addOneErlangLine(initFuncName + "() -> ");
        indent++;

        boolean isUniProcess = ast.getClass().equals(AST.UniprocessObj.getClass());

        int eqCount = 0;
        for (int i = 0; i < allProcessNames.size(); i++) {
            String processName = allProcessNames.get(i);
            String functionName = getProcessStartFunctionName(ErlangProcessContext.createProcessName(processName));
            String line;
            if (isUniProcess) {
                line = functionName + "(" + eqCount + ")";
            } else {
                int index = symTab.FindProcess(processName);
                if (index >= symTab.processes.size()) {
                    throw new PcalErlangGenException(
                            "Process with name \"" + processName + "\" could not be found in the symbol table."
                    );
                }
                PcalSymTab.ProcessEntry processEntry = (PcalSymTab.ProcessEntry) symTab.processes.get(index);

                if (processEntry.isEq) {
                    line = functionName + "(" + eqCount + ")";
                    eqCount++;
                } else {
                    String ids = exprConverter.TLAExprToErlangStr(processEntry.id, new ErlangDefinitionContext("", allConstantVarNames));
                    line = String.format(START_FUNC_INIT_PROCESS_SET, functionName, ids);
                }
            }
            if (i != allProcessNames.size() - 1) {
                line += ",";
            } else {
                line += ".";
            }
            addOneErlangLine(line);
        }
        addFuncToExports(initFuncName, 0);
        indent--;
        addOneErlangLine("");

        String runFuncName = "run";
        addOneErlangLine(runFuncName + "() -> ");
        indent++;
        addOneErlangLine(String.format(BROADCAST_STATEMENT, "'go'") + ".");
        indent--;
        addFuncToExports(runFuncName, 0);
    }

    @SuppressWarnings("unchecked")
    private Map<String, String> parseDefinitions(TLAExpr defs) throws PcalErlangGenException {
        /*
         * Contains all definitions. It is a mapping of PlusCal identifiers to translated Erlang values
         */
        Map<String, String> definitions = new TreeMap<>(String.CASE_INSENSITIVE_ORDER);

        ErlangDefinitionContext context = new ErlangDefinitionContext("", allConstantVarNames);
        for (Object defObj : defs.tokens) {
            Vector<TLAToken> def = (Vector<TLAToken>) defObj;
            // parse definition
            Map.Entry<String, String> defErlang = this.exprConverter.parseDefinition(def, context);
            String pcalName = defErlang.getKey();
            definitions.put(pcalName, defErlang.getValue());
        }
        // add all to global constant map
        allConstantVarNames.putAll(context.getConstantNamesMap());
        return definitions;
    }

    private void addInitialization() {
        // add module, imports, export functions, macros etc.
        String moduleName = getErlangModuleName(PcalParams.TLAInputFile);
        addOneErlangLine(String.format(MODULE_DECL, moduleName) + ".");
        addOneErlangLine(EXPORT_DECL + ".");
        exportedFuncsPos = erlangCode.size() - 1; // save index of exports
        addOneErlangLine(String.format(MACRO_DEFINITION, IS_TEST, "false"));

        updateEndOfModuleAttributePos(erlangCode.size() - 1);
        endOfFunctionPos = endOfModuleAttributesPos + 2;

        addOneErlangLine(""); // empty line
    }

    private void GenUniprocess(AST.Uniprocess ast) throws PcalErlangGenException {
        GenProcess(ast.name, ast.decls, ast.body);
    }

    private void GenMultiprocess(AST.Multiprocess ast) throws PcalErlangGenException {
        for (Object processObj : ast.procs) {
            AST.Process process = (AST.Process) processObj;
            GenProcess(process.name, process.decls, process.body);
        }
    }

    private void GenProcess(String name, Vector varDecls, Vector body) throws PcalErlangGenException {
        /*
          Create process context
         */

        ErlangProcessContext context = new ErlangProcessContext(name, varDecls);

        // add function for process
        String processFuncName = context.getProcessName();
        String firstStateVarName = context.getCurrentStateVarName();
        String line = processFuncName + "(" + firstStateVarName + ")" + " -> ";
        addOneErlangLine(line);
        indent++; // incr indentation level

        /*
          Add registration of process as first statement of body:
           erla_libs:register_proc(State0#state_Server.proc_ID)
         */
        addOneErlangLine(String.format(SINGLE_LINE_COMMENT, "Register process globally"));
        String selfStr = context.getErlangVarStr("self");
        addOneErlangLine(String.format(REGISTER_STATEMENT, selfStr) + ",");
        addOneErlangLine("");

        if (PcalParams.GenErlangMainFunction) {
            /*
                Add 'receive' block for waiting before all processes are registered
            */
            addOneErlangLine(String.format(SINGLE_LINE_COMMENT, "Wait for 'go' message"));
            addOneErlangLine("receive");
            indent++;
            addOneErlangLine("go -> ok");
            indent--;
            addOneErlangLine("end,");
            addOneErlangLine("");
        }

        /*
            Generate body
         */

        addOneErlangLine(String.format(SINGLE_LINE_COMMENT, "Body"));
        GenLabeledBody(body, context);

        EndBody();

        indent = 0; // reset indent level

        /*
          Generate state

            Note: we generate the state after the body so that we have discovered all constants.
         */

        GenProcessState(context, varDecls);

        /*
            Export function
         */

        addFuncToExports(processFuncName, 1);

        /*
          Generate initialization function
         */
        GenProcessStartFunction(context);

        /*
            Add constants to global set
         */

        allConstantVarNames.putAll(context.getConstantNamesMap());
    }



    private void GenProcessStartFunction(ErlangProcessContext context) throws PcalErlangGenException {
        String procStartFuncName = getProcessStartFunctionName(context.getProcessName());
        String argumentStr = "Id";
        addOneErlangLine(procStartFuncName + "(" + argumentStr + ") ->");
        indent++;

        /*
          Add spawn link line:
           spawn_link(?MODULE, process_myName, [#state_myName{proc_ID = Id}])
         */

        String processNameWithPrefix = context.getProcessName();
        String procRecordName = "#" + context.getStateRecordName();
        String initRecordStr = procRecordName + "{" + context.getFieldName("self") + " = " + argumentStr + "}";
        String spawnLinkLine = "spawn_link(?MODULE, " + processNameWithPrefix + ", " + "[" + initRecordStr + "]).";

        addOneErlangLine(spawnLinkLine);

        indent--;
        addOneErlangLine("");

        /*
          Add to exported functions
         */
        addFuncToExports(procStartFuncName, 1);
    }

    /**
     * Generates a record to represent the state (all process-local variables).
     *
     * @param context  the context of the process.
     * @param varDecls the variable declarations of the current process
     */
    private void GenProcessState(ErlangProcessContext context, Vector varDecls) throws PcalErlangGenException {
        // generate record
        Vector<String> recordVec = new Vector<>();
        String recordName = context.getStateRecordName();
        recordVec.addElement("-record(" + recordName + ", " + "{");
        indent++;

        // fill with fields that are common for all processes
        String numLine = formatLineForIndent(context.getFieldName("self") + " = " + "-1", indent);

        if (!varDecls.isEmpty()) {
            numLine += ",";
        }
        recordVec.addElement(numLine);

        // fill with variable declarations
        if (!varDecls.isEmpty()) {
            context.beginVarDeclScope();
            for (int i = 0; i <= varDecls.size() - 1; i++) {
                AST.VarDecl varDecl = (AST.VarDecl) varDecls.get(i);
                String varName = context.getFieldName(varDecl.var); // get erlang var name
                String value;
                if (isFunction(varDecl)){
                    value = GenFunction(varDecl,context); // todo: probably obsolete, remove when functions are implemented
                } else {
                    value = TLAExprToErlangStr(varDecl.val, context);
                }

                String line = formatLineForIndent(varName + " = " + value, indent);
                if (!(i == varDecls.size() - 1)) {
                    line += ",";
                }
                recordVec.addElement(line);
            }
            context.endVarDeclScope();
        }

        indent--;
        // end record declaration
        recordVec.addElement("}).");
        recordVec.addElement(""); // empty line
        // write to file vector
        addMultipleErlangLinesAtIndex(recordVec, endOfModuleAttributesPos + 1);
        // update end of attributes position
        updateEndOfModuleAttributePos(endOfModuleAttributesPos + recordVec.size());
    }

    private boolean isFunction(AST.VarDecl varDecl) {
        return false; // disable function translation
    }

    private String GenFunction(AST.VarDecl varDecl, ErlangProcessContext context) throws PcalErlangGenException {
        Vector<TLAToken> tokens = (Vector<TLAToken>) varDecl.val.tokens.get(0);
        tokens.remove(0);
        tokens.remove(tokens.size()-1);
        int getIndexOfOp = -1;
        for (int i = 0; i < tokens.size(); i++) {
            TLAToken token = tokens.get(i);
            if (token.string.equals("|->")){
                getIndexOfOp = i;
                break;
            }
        }

        List<TLAToken> sets = tokens.subList(0,getIndexOfOp);
        //TODO Hacky way to circument the normal in operator translation
        for (TLAToken tok : sets){
            if (tok.string.equals("\\in")){
                tok.string = "\\inFunction";
            }
        }
        List<TLAToken> function = tokens.subList(getIndexOfOp + 1, tokens.size());

        List<Integer> listOfSeparators = findSeparators(sets);
        List<String> listOfVars = new ArrayList<>();
        List<List<TLAToken>> separatedSets = new ArrayList<>();

        listOfSeparators.add(sets.size());
        int lastSep = 0;
        for (Integer i: listOfSeparators) {
            separatedSets.add(sets.subList(lastSep,i));
            lastSep = i+1;
        }
        for (List<TLAToken> tok : separatedSets){
            listOfVars.add(tok.get(0).string);
        }

        ErlangFunctionContext funContext = new ErlangFunctionContext(context,listOfVars);
        List<String> translatedSets = new ArrayList<>();
        for (List<TLAToken> set : separatedSets) {
            Vector vec = new Vector<>(set);
            Vector endVec = new Vector<>();
            endVec.add(vec);
            String setExpr = exprConverter.TLAExprToErlangStr(new TLAExpr(endVec),funContext);
            translatedSets.add(setExpr);
        }

        Vector vec = new Vector<>(function);
        Vector endVec = new Vector<>();
        endVec.add(vec);
        String funExpr = exprConverter.TLAExprToErlangStr(new TLAExpr(endVec),funContext);
        String funString = "fun(";

        StringBuilder functionArgs = new StringBuilder();
        for(String set : translatedSets) {
            functionArgs.append(set.split("===")[0]);
            functionArgs.append(",");
        }
        functionArgs = new StringBuilder(functionArgs.substring(0, functionArgs.length() - 1));


        funString += functionArgs + ") -> {" + functionArgs + "}, " + funExpr + " end";

        //String Construction
        StringBuilder result = new StringBuilder("[{");
        result.append(functionArgs);
        result.append("} || ");

        for (String set : translatedSets){
            result.append(set.split("===")[0]).append(" <- ").append("sets:to_list( ").append(set.split("===")[1]).append(") ,");
        }
        result = new StringBuilder(result.substring(0, result.length() - 1));
        result.append("]");

        result = new StringBuilder(String.format(INITIAL_FUNCTION_DECL, funString, result));
        return result.toString();
    }

    private List<Integer> findSeparators(List<TLAToken> sets) {
        List<TLAToken> castSets = sets;
        List<Integer> res = new ArrayList<>();
        int openBrackets = 0;
        for (int i = 0; i < sets.size(); i++) {
            if ( castSets.get(i).string.equals("{")){
                openBrackets++;
            }else if (castSets.get(i).string.equals("}")){
                openBrackets--;
            }else if(openBrackets == 0) {
                if(castSets.get(i).string.equals(",")){
                    res.add(i);
                }
            }
        }
        return res;
    }


    private void GenBody(Vector body, ErlangProcessContext context) throws PcalErlangGenException {
        for (int i = 0; i < body.size(); i++) {
            AST stmt = (AST) body.elementAt(i);
            if (stmt.getClass().equals(AST.ReceiveCallObj.getClass())) {
                List<AST> followingStmts = body.subList(i + 1, body.size()); // care: not a copy
                GenReceiveCall((AST.ReceiveCall) stmt, followingStmts, context);
                break;
            }
            GenStmt(stmt, context);
        }
    }

    private void GenLabeledBody(Vector body, ErlangProcessContext context) throws PcalErlangGenException {
        // add all statements in one vector
        Vector allStmts = new Vector();
        for (int i = 0; i < body.size(); i++) {
            AST.LabeledStmt ls = (AST.LabeledStmt) body.elementAt(i);
            allStmts.addAll(ls.stmts);
        }
        // translate statements
        GenBody(allStmts, context);
    }

    /**
     * Removes the last comma or replaces it with a full-stop.
     * This is to be called e.g. when a body is generated, in which each line
     * is ended with a comma (as is usual in erlang functions).
     */
    private void EndBody() {
        ChangePunctuation(".");
    }

    private void ChangePunctuation(String punctuation) {
       ChangePunctuation(punctuation, currentPos - 1);
    }

    private void ChangePunctuation(String punctuation, int index) {
        String lastLine = getErlangLine(index);
        assert lastLine != null;
        if (lastLine.isBlank() || isCommentLine(lastLine)) {
            // skip whitespace or comment lines
            ChangePunctuation(punctuation, index - 1);
        } else {
            // remove last comma before adding new punctuation and end statement block with the given punctuation
            String newLine = lastLine.substring(0, lastLine.length() - 1) + punctuation;
            // update
            updateErlangLine(index, newLine);

            if (punctuation.equals("."))
                addOneErlangLine("");
        }
    }

    private boolean isCommentLine(String line) {
        // remove (all) leading whitespace
        String trimmedLine = line.trim();
        try {
            // get first char of trimmed line
            char firstChar = trimmedLine.charAt(0);
            return firstChar == COMMENT_CHAR;
        } catch (IndexOutOfBoundsException e) {
            return false;
        }
    }

    private void GenStmt(AST ast, ErlangProcessContext context) throws PcalErlangGenException {
        if (ast.getClass().equals(AST.AssignObj.getClass()))
            GenAssign((AST.Assign) ast, context);
        else if (ast.getClass().equals(AST.IfObj.getClass()))
            GenIf((AST.If) ast, context);
        else if (ast.getClass().equals(AST.LabelIfObj.getClass()))
            GenLabelIf((AST.LabelIf) ast, context);
        else if (ast.getClass().equals(AST.WhileObj.getClass()))
            GenWhile((AST.While) ast, context);
        else if (ast.getClass().equals(AST.EitherObj.getClass()))
            GenEither((AST.Either) ast, context);
        else if (ast.getClass().equals(AST.WithObj.getClass()))
            GenWith((AST.With) ast, context);
        else if (ast.getClass().equals(AST.WhenObj.getClass()))
            GenWhen((AST.When) ast, context);
        else if (ast.getClass().equals(AST.PrintSObj.getClass()))
            GenPrintS((AST.PrintS) ast, context);
        else if (ast.getClass().equals(AST.AssertObj.getClass()))
            GenAssert((AST.Assert) ast, context);
        else if (ast.getClass().equals(AST.SkipObj.getClass()))
            GenSkip((AST.Skip) ast, context);
        else if (ast.getClass().equals(AST.SendCallObj.getClass()))
            GenSendCall((AST.SendCall) ast, context);
        else if (ast.getClass().equals(AST.ReceiveCallObj.getClass()))
            throw new PcalErlangGenException("Receive reached in GenStmt!");
        else if (ast.getClass().equals(AST.FailObj.getClass()))
            GenFail((AST.Fail) ast, context);
        else if (ast.getClass().equals(AST.MaybeFailObj.getClass()))
            GenMaybeFail((AST.MaybeFail) ast, context);
        else
            PcalDebug.ReportBug("Unexpected AST type " + ast);
    }

    private void GenLabelIf(AST.LabelIf ast, ErlangProcessContext context) throws PcalErlangGenException {
        Vector<AST> allThenStmts = new Vector<AST>(ast.unlabThen);
        Vector<AST> allElseStmts = new Vector<AST>(ast.unlabElse);

        for (Object stmtObj : ast.labThen) {
            allThenStmts.addAll(((AST.LabeledStmt) stmtObj).stmts);
        }

        for (Object stmtObj : ast.labElse) {
            allElseStmts.addAll(((AST.LabeledStmt) stmtObj).stmts);
        }

        GenGeneralIf(ast.test, allThenStmts, allElseStmts, context);
    }

    private void GenGeneralIf(TLAExpr test, Vector<AST> thenStmts, Vector<AST> elseStmts, ErlangProcessContext context) throws PcalErlangGenException {
        ErlangProcessContext elseContext = new ErlangProcessContext(context, false);
        String originalStateVarName = context.getCurrentStateVarName();
        String condExpr = TLAExprToErlangStr(test, context);
        String caseLine = "case " + condExpr + " of";
        String trueLine = "true ->";
        String falseLine = "false ->";
        String endLine = "end,";
        addOneErlangLine(caseLine);
        addOneErlangLine(trueLine);
        indent++;
        GenBody(thenStmts, context);
        addOneErlangLine(getErlangNullStmt());

        int thenIndent = indent;
        int thenVarNum = context.getStateVarNum();

        // Last line of then needs to be semicolon (commented out because of null statement)
        // ChangePunctuation(";");

        indent--;
        addOneErlangLine(falseLine);
        int falseLineIndent = indent; // save "false"-line indentation for later
        indent++;

        for (AST stmt : elseStmts) {
            GenStmt(stmt, elseContext);
        }

        if(elseStmts.isEmpty() && elseContext.getStateVarNum() == thenVarNum &&
                !elseContext.getCurrentStateVarName().equals(originalStateVarName)) {
            /*
                Increment state var in this case so that we prevent a reassignment of the last state variable
             */
            String currentStateVarName = elseContext.getCurrentStateVarName();
            String nextStateVarName = elseContext.nextStateVarName();
            addOneErlangLine(nextStateVarName + " = " + currentStateVarName + ",");
        }

        int elseVarNum = elseContext.getStateVarNum();

        if (thenVarNum > elseVarNum) {
            // then branch has newer version
            // sync else branch's state name with then branch
            String elseStateVarName = elseContext.getCurrentStateVarName();
            String updatedStateName = elseContext.changeStateVarName(thenVarNum);
            addOneErlangLine(updatedStateName + " = " + elseStateVarName + ",");
        } else if (thenVarNum < elseVarNum) {
            // else branch has newer version
            // sync then branch's state name with else branch
            String thenStateVarName = context.getCurrentStateVarName();
            String updatedStateName = context.changeStateVarName(elseVarNum);
            int thenEndIndex = getLinePosBeforeCurrentPos(currentPos, falseLine, falseLineIndent);
            if (thenEndIndex < 0) {
                // should never really happen if the search function works correctly
                throw new PcalErlangGenException("The position of the false branch could not be found");
            }
            String thenEndLine = getErlangLine(thenEndIndex - 1);
            assert(thenEndLine != null && thenEndLine.contains(getErlangNullStmt()));
            insertErlangLineAtIndex(thenEndIndex - 1,
                    updatedStateName + " = " + thenStateVarName  + ",",
                    thenIndent);
        }

        addOneErlangLine(getErlangNullStmt());

        // Last line of Else, does not need a comma
        ChangePunctuation("");

        indent--;
        addOneErlangLine(endLine);
    }

    private void GenWhile(AST.While ast, ErlangProcessContext context) throws PcalErlangGenException {
        /*
          Inline code
         */
        String while_func_name = context.getAndIncrementWhileFunc();
        String while_func = while_func_name + "(" + context.getCurrentStateVarName() + "),";
        String while_line = context.nextStateVarName() + " = " + while_func;
        addOneErlangLine(while_line);

        /*
          Function Code
         */
        int savedIndent = indent;
        int savedCurrentPos = currentPos;
        int savedEndOfFuncPos = endOfFunctionPos;

        currentPos = endOfFunctionPos;
        // to have the states inside the while function be independent
        ErlangProcessContext whileContext = new ErlangProcessContext(context, true);
        indent = 0;

        addOneErlangLine("");
        String originalStateVarName = whileContext.getCurrentStateVarName();
        addOneErlangLine(while_func_name + "(" + originalStateVarName + ") " + "->");
        indent++;

        String testString = TLAExprToErlangStr(ast.test, whileContext);
        addOneErlangLine("case");

        addOneErlangLine(testString + " of");
        indent++;
        addOneErlangLine("true ->");
        indent++;
        // add unlabeled statements first and then all labeled ones
        Vector allStmts = new Vector(ast.unlabDo);
        for (int i = 0; i < ast.labDo.size(); i++) {
            AST.LabeledStmt ls = (AST.LabeledStmt) ast.labDo.elementAt(i);
            allStmts.addAll(ls.stmts);
        }
        // generate body
        GenBody(allStmts, whileContext);
        addOneErlangLine(while_func_name + "(" + whileContext.getCurrentStateVarName() + ");");
        indent--;
        String trueLine = "false ->";
        addOneErlangLine(trueLine);
        indent++;
        addOneErlangLine(originalStateVarName);
        indent--;
        indent--;
        addOneErlangLine("end.");
        addOneErlangLine("");

        //TODO check if this is correct, probably not in all edgecases
        int save = currentPos;
        currentPos = savedCurrentPos + (currentPos - savedEndOfFuncPos);
        endOfFunctionPos = save;
        indent = savedIndent;
    }

    private void GenSkip(AST.Skip ast, ErlangProcessContext context) {
        /*
          Generate a comment so that the user (and we, too) is not perplexed by a missing statement.
          Todo: improve EndBody to put the full-stop at the end of a comment (possibly a new line).
         */
        String line = String.format(SINGLE_LINE_COMMENT, "skip");
        addOneErlangLine(line);
    }

    private void GenAssert(AST.Assert ast, ErlangProcessContext context) throws PcalErlangGenException {
        // import module if it was not already
        if (!isModuleImported()) {
            importErlangModule();
        }

        String aExpr = TLAExprToErlangStr(ast.exp, context);
        String assertLine = "?assert(" + aExpr + "),";
        addOneErlangLine(assertLine);
    }

    private void GenPrintS(AST.PrintS sPrint, ErlangProcessContext context) throws PcalErlangGenException {
        String sExpr = TLAExprToErlangStr(sPrint.exp, context);
        String line = String.format(PRINT_STATEMENT, sExpr) + ",";
        addOneErlangLine(line);
    }

    private void GenWhen(AST.When ast, ErlangProcessContext context) throws PcalErlangGenException {
        throw new PcalErlangGenException("Not implemented", ast);
    }

    private void GenWith(AST.With ast, ErlangProcessContext context) throws PcalErlangGenException {
        if (!ast.isEq) {
            throw new PcalErlangGenException("Translation of \\in assignments is not implemented yet", ast);
        }

        String varName = context.addTemporaryVar(ast.var);
        String value = TLAExprToErlangStr(ast.exp, context);

        // add to code
        addOneErlangLine(String.format(TEMP_VAR_ASSIGNMENT, varName, value) + ",");
        GenBody(ast.Do, context);

        context.removeTemporaryVar(ast.var);
    }

    private void GenEither(AST.Either ast, ErlangProcessContext context) throws PcalErlangGenException {
        throw new PcalErlangGenException("Not implemented", ast);
    }

    private void GenIf(AST.If ast, ErlangProcessContext context) throws PcalErlangGenException {
        GenGeneralIf(ast.test, ast.Then, ast.Else,context);
    }

    private void GenAssign(AST.Assign ast, ErlangProcessContext context) throws PcalErlangGenException {
        for (int i = 0; i < ast.ass.size(); i++) {
            AST.SingleAssign sAssign = (AST.SingleAssign) ast.ass.elementAt(i);
            GenSingleAssign(sAssign, context);
        }
    }

    private void GenSingleAssign(AST.SingleAssign sAssign, ErlangProcessContext context) throws PcalErlangGenException {
        // add to code
        addOneErlangLine(exprConverter.parseAssignment(sAssign.lhs, sAssign.rhs, context));
    }

    /**
     * Translate Receive(message).
     *
     * @param ast The AST object
     * @param followingStmts All statements that follow the receive operation
     * @param context The process' context
     */
    private void GenReceiveCall(AST.ReceiveCall ast, List<AST> followingStmts, ErlangProcessContext context) throws PcalErlangGenException {
        /*
          Get all info
         */

        // get message var name and state var name
        context.nextMessageVarName();
        String currMessageVarName = context.getCurrentMessageVarName();
        String fieldName = context.getFieldName(ast.targetVarName); // todo: investigate whether this needs to be changed to ast.targetExp

        // create line to assign pattern-matched temp message var to state var
        String messageAssignLine = formatVarAssignment(fieldName, currMessageVarName, context);

        /*
          Generate erlang code
         */

        // add receive keyword
        String receiveKeyword = "receive";
        addOneErlangLine(receiveKeyword);
        indent++;
        // add pattern matching of message
        String patternMatchLine = String.format("%s ->", currMessageVarName);
        addOneErlangLine(patternMatchLine);
        indent++;

        // assign pattern matched var to state var
        addOneErlangLine(messageAssignLine);

        Vector stmts = new Vector(followingStmts);
        GenBody(stmts, context);
        ChangePunctuation("");
        indent--;
        indent--;
        String endReceiveLine = "end,";
        addOneErlangLine(endReceiveLine);
    }

    private void GenSendCall(AST.SendCall ast, ErlangProcessContext context) throws PcalErlangGenException {
        /*
          Translate Send(message, receiver);
         */
        String sendLine;
        String messageStr = TLAExprToErlangStr(ast.message, context);

        if (ast.type == SendType.SEND) {
            String receiverStr = TLAExprToErlangStr(ast.receiver, context);
            sendLine = String.format(SEND_STATEMENT, receiverStr, messageStr);
        } else if (ast.type == SendType.BROADCAST) {
            sendLine = String.format(BROADCAST_STATEMENT, messageStr);
        } else {
            throw new PcalErlangGenException("Encountered unknown send type: " + ast.type);
        }
        sendLine += ",";

        addOneErlangLine(sendLine);
    }

    private void GenMaybeFail(AST.MaybeFail ast, ErlangProcessContext context) {
        addOneErlangLine("% maybeFail");
    }

    private void GenFail(AST.Fail ast, ErlangProcessContext context) {
        // todo: change this to behave like the PlusCal primitive, i.e. stay in a non-terminating loop
        addOneErlangLine("% fail");
    }

    /**
     * Adds the input to a new line in the Erlang file with correct indentation.
     *
     * @param line The line that is to be added
     */
    private void addOneErlangLine(String line) {
        erlangCode.add(currentPos, formatLineForIndent(line, indent));
        currentPos++;
    }

    private String formatLineForIndent(String line, int indent) {
        return " ".repeat(indent * NUM_SPACES_FOR_INDENT) + line;
    }

    private String getErlangLine(int index) {
        try {
            return erlangCode.get(index);
        } catch (IndexOutOfBoundsException e) {
            return null;
        }
    }

    private void updateErlangLine(int index, String newLine) {
        erlangCode.set(index, newLine);
    }

    private void importErlangModule() {
        erlangCode.add(endOfModuleAttributesPos, "-include_lib(\"" + "stdlib/include/assert.hrl" + "\").");
        updateEndOfModuleAttributePos(endOfModuleAttributesPos + 1);
        currentPos++;
    }

    private boolean isModuleImported() {
        for (int i = 0; i < endOfModuleAttributesPos; i++) {
            if (erlangCode.get(i).equals("-include_lib(\"" + "stdlib/include/assert.hrl" + "\")."))
                return true;
        }
        return false;
    }

    private void addMultipleErlangLinesAtIndex(Vector<String> lines, int index) {
        erlangCode.addAll(index, lines);
        if (currentPos > index) {
            currentPos += lines.size();
        }
    }

    private void insertErlangLineAtIndex(int index, String line, int indent) {
        erlangCode.add(index, formatLineForIndent(line, indent));
        if (currentPos > index) {
            currentPos++;
        }
    }

    /**
     * Returns the last position to match the given line until the given position in the erlang code is reached
     * @param untilPos the position until which the search is conducted
     * @param line the line to search in the erlang code
     * @param indent the indentation of the line parameter
     * @return the last position to match the given line until the given position in the erlang code is reached
     */
    private int getLinePosBeforeCurrentPos(int untilPos, String line, int indent) {
        List<String> domain = erlangCode.subList(0, untilPos);
        return domain.lastIndexOf(formatLineForIndent(line, indent));
    }

    private String TLAExprToErlangStr(TLAExpr expr, ErlangProcessContext context) throws PcalErlangGenException {
        return exprConverter.TLAExprToErlangStr(expr, context);
    }

    /**
     * Adds the process with the given name to the exported functions declaration
     *
     * @param name The name of the process to be added
     */
    private void addFuncToExports(String name, int arity) {
        String exportedFuncs = getErlangLine(exportedFuncsPos);
        int insertPos;
        // search for the last '/' char that comes before the arity of the last erlang function entry
        assert exportedFuncs != null;
        int lastArityDelimiterIndex = exportedFuncs.lastIndexOf("/");
        String decl = "";
        if (lastArityDelimiterIndex == -1) {
            // export list is empty
            insertPos = exportedFuncs.indexOf("[") + 1;
        } else {
            // export list contains exports
            insertPos = lastArityDelimiterIndex + 2;
            decl = ", "; // add comma after previous export declaration
        }
        decl += name + "/" + arity;
        String left = exportedFuncs.substring(0, insertPos);
        String right = exportedFuncs.substring(insertPos);
        String newExports = left + decl + right;
        updateErlangLine(exportedFuncsPos, newExports);
    }

    /**
     * Gets the erlang file name.
     *
     * @return The erlang file name (without extension).
     */
    public static String getErlangFileName() { // todo: find a way to do the file name creation only once
        String pcalFileName = PcalParams.TLAInputFile;
        int firstLetter = pcalFileName.lastIndexOf(File.separator) + 1;
        // make first letter of the module name lowercase
        char[] c = pcalFileName.toCharArray();
        c[firstLetter] = Character.toLowerCase(c[firstLetter]);
        return new String(c);
    }

    private static String getErlangModuleName(String pcalFileName) {
        // get module name
        String moduleName = pcalFileName.substring(pcalFileName.lastIndexOf(File.separator) + 1);

        // make first letter lowercase (for it to be an atom)
        return Character.toLowerCase(moduleName.charAt(0)) + moduleName.substring(1);
    }

    public static List<String> getErlaLibsModuleNames() {
        // todo: return only modules that are used in the generated code
        return Arrays.asList(ERLA_LIBS_MODULE_COMMUNICATION_NAME, ERLA_LIBS_MODULE_SETS_NAME, ERLA_LIBS_MODULE_UTIL_NAME);
    }

    /**
     * Updates the endOfModuleAttributePos variable and adjust other variables accordingly.
     *  Always use this to update endOfModuleAttributePos.
     * @param newPos The new position of the end of the module attributes
     */
    private void updateEndOfModuleAttributePos(int newPos){
        int diff = newPos - endOfModuleAttributesPos;
        endOfModuleAttributesPos = newPos;
        endOfFunctionPos += diff;
    }

    private String getErlangNullStmt() {
        return "ok;";
    }

    private void generateConstantDeclarations(Map<String, String> parsedDefinitions) {
        // add constants
        for (Map.Entry<String, String> constant : allConstantVarNames.entrySet()) {
            if (parsedDefinitions.containsKey(constant.getKey())) {
                addDefinition(constant.getValue(), parsedDefinitions.get(constant.getKey()));
            } else {
                addConstant(constant.getValue());
            }
        }
    }

    private void addDefinition(String constant, String initValue) {
        addConstant(constant, initValue);
    }

    private void addConstant(String constant, String initValue) {
        insertErlangLineAtIndex(
                endOfModuleAttributesPos,
                String.format(MACRO_DEFINITION, constant, initValue), indent
        );
        updateEndOfModuleAttributePos(endOfModuleAttributesPos + 1);
    }

    private void addConstant(String constant) {
        addConstant(constant, MACRO_INIT_VALUE);
    }

    private String getProcessStartFunctionName(String processName) {
        return PREFIX_PROCESS_START_FUNC + processName;
    }

}