
/***************************************************************************
* CLASS AST                                                                *
*                                                                          *
* This class defines AST objects, which represent non-terminals of the     *
* +CAL grammar, to be subclasses of the AST class.                         *
*                                                                          *
* Each subclass has a toString() method that prints the object as the      *
* TLA+ record that represents that node in the representation of the       *
* abstract syntax tree used in the PlusCal TLA+ specification.             *
*                                                                          *
* There are no explicit classes corresponding to the following             *
* non-terminals.                                                           *
*                                                                          *
*    Algorithm   AlgorithmBody LabelSeq   SimpleStmt   Finalstmt  VarDecls *
*                                                                          *
* However, there are the following classes that do not represent explicit  *
* non-terminals of the +CAL grammar.                                       *
*                                                                          *
* Uniprocess   MultiProcess   SingleAssign   CallReturn   CallGoto         *
*                                                                          *
* Every AST has col and line fields that contain the position of the       *
* first character of the corresponding portion of the algorithm text (as   *
* human ordinals, numbered starting from 1).                               *
*                                                                          *
*                                                                          *
* Since the only way Java has of defining record (struct) type is by       *
* making it a class, all the different AST node subtypes had to be         *
* subclasses.  I didn't want to put each of them in a separate file, so I  *
* made them all nested inner static classes in this file.  (I presume it   *
* doesn't make sense to make them dynamic classes, since that would imply  *
* that each instance of an AST node has its own separate instance of       *
* those classes.  Anyway, we Java produces a runtime NoSuchMethodError     *
* unless I make the inner classes static.)                                 *
*                                                                          *
* To enable a method to figure out what subclass an AST object is, I       *
* initially gave the class a type field and tried to use that field to     *
* determine the type.  However, this didn't work right at all.  The        *
* problem is that when an element of the subtype gets obtained as an       *
* object of the superclass AST--for example, when it's pulled out of a     *
* vector of AST objects, the type field of the resulting object is set to  *
* the value set by the supertype's constructor.  So, I need to actually    *
* find out what Java thinks the class of the object is.  The following     *
* hack seems to work.  To determine if the subclass of an AST object obj   *
* is Skip, one can test                                                    *
*                                                                          *
*    obj.getClass().toString().equals("class pcal.AST$Skip")               *
*                                                                          *
* However, this seems unlikely to work for all versions of all Java        *
* implementations.  So, for each subclass like AST.Skip, we define an      *
* object SkipObj of that class.  We then test if obj is of class AST.Skip  *
* by                                                                       *
*                                                                          *
*    obj.getClass().equals(AST.SkipObj.getClass())                         *
*                                                                          *
* The object SkipObj cannot be declared with an initial value, because     *
* that leads the initialization of the AST class to go into an infinite    *
* loop.  So, the method AST.ASTInit() assign a new AST.Skip node to        *
* AST.SkipObj.                                                             *
*                                                                          *
* I'm sure there's a better way, but I can't find anything about           *
* it in the Java Reference Manual.                                         *
***************************************************************************/
package pcal;
import pcal.exception.ParseAlgorithmException;
import pcal.exception.TLAExprException;

import java.util.Vector;

public class AST implements Cloneable {
    public static AST.Uniprocess UniprocessObj;
    public static AST.Multiprocess MultiprocessObj;
    public static AST.Procedure ProcedureObj;
    public static AST.Process ProcessObj;
    public static AST.VarDecl VarDeclObj;
    public static AST.PVarDecl PVarDeclObj;
    public static AST.LabeledStmt LabeledStmtObj;
    public static AST.While WhileObj;
    public static AST.Assign AssignObj;
    public static AST.SingleAssign SingleAssignObj;
    /*********************************************************************
     * We added an explicit SINGLEASSIGN type to represent a single       *
     * assignment within a multi-assignment.  We did this because Java    *
     * doesn't allow a record (struct) to be constructed as anything      *
     * other than an object of some class.                                *
     *********************************************************************/
    public static AST.Lhs LhsObj;
    public static AST.If IfObj;
    public static AST.Either EitherObj;
    public static AST.With WithObj;
    public static AST.When WhenObj;
    public static AST.PrintS PrintSObj;
    public static AST.Assert AssertObj;
    public static AST.Skip SkipObj;
    public static AST.LabelIf LabelIfObj;
    public static AST.LabelEither LabelEitherObj;
    public static AST.Clause ClauseObj;
    /*********************************************************************
     * Because Java doesn't have records, only objects, we we add an      *
     * explicit Clause object to be a record such that the `clauses'      *
     * field of a LabelEither object is a sequence of Clause objects.     *
     *********************************************************************/
    public static AST.Call CallObj;
    public static AST.Return ReturnObj;
    public static AST.CallReturn CallReturnObj;
    public static AST.CallGoto CallGotoObj;
    public static AST.Goto GotoObj;
    public static AST.Macro MacroObj;
    public static AST.MacroCall MacroCallObj;

    public static AST.SendCall SendCallObj;
    public static AST.ReceiveCall ReceiveCallObj;
    public static AST.GetAllProcsCall GetAllProcsCallObj;
    public static AST.Fail FailObj;
    public static AST.MaybeFail MaybeFailObj;

    public int col;
    public int line;
    /*********************************************************************
     * These are the column and line numbers of the first token in the    *
     * algorithm text that corresponds to the AST. (They are human        *
     * ordinals, counting from 1.)                                        *
     *********************************************************************/
    public int macroCol = 0;
    public int macroLine = -1;
    /*********************************************************************
     * If this is an object that was inserted into the AST as the result  *
     * of macro expansion, then this is the column and line number of     *
     * the MacroCall object that was expanded.  The col and line values   *
     * give the position of the object in the macro definition that       *
     * yielded the current object when the macro was expanded.            *
     *                                                                    *
     * If the object was not inserted by macro expansion, then macroLine  *
     * equals -1.                                                         *
     *********************************************************************/

    /**
     * If this AST is a statement that is the first statement resulting from
     * expansion of a macro call , then macroOriginBegin is set to the
     * origin.begin value of the macro call.  It is set by
     * ParseAlgorithm.ExpandMacroCall and is used by PcalTLAGen.GenLabeledStmt
     * to set the MappingObject.LeftParen that marks the beginning of the
     * labeled statement's translation.
     * <p>
     * macroOriginEnd is similarly set for the last statement resulting from
     * the expansion of a mapping call and used to set the labeled statement's
     * translation's MappingObject.RightParen.
     * <p>
     * This is a Kludge to correct a bug in the TLA+ translation to
     * PlusCal mapping.  These kludges are the result of implementing
     * that mapping on top of the existing translator, rather than rewriting
     * the translation.
     */
    public PCalLocation macroOriginBegin = null;
    public PCalLocation macroOriginEnd = null;

    public String lbl = "";
    /*********************************************************************
     * Added by LL on 3 Mar 2006.  Used to hold a statement's label       *
     * during the parsing process, but irrelevant once the final AST has  *
     * been constructed.                                                  *
     *********************************************************************/

    /**
     * If the lbl field is not the empty string "", then lblLocation is
     * the location of the beginning of the label that provided the string
     * if it came from a label written by the user.  It will be null if the
     * label was added by the translator.
     */
    public PCalLocation lblLocation = null;

    /**
     * The region of the PlusCal code from which the object was created.
     */
    private Region origin = null;

    public Region getOrigin() {
        return origin;
    }

    public void setOrigin(Region origin) {
        this.origin = origin;
    }

    public String location()
    /*********************************************************************
     * The string that describes the location in the algorithm of the     *
     * first token that represents the AST object.  Should be used in     *
     * error messages.                                                    *
     *********************************************************************/
    {
        if (macroLine < 0) {
            return "line " + line + ", column " + col;
        } else {
            return "line " + line + ", column " + col +
                    " of macro called at line " + macroLine +
                    ", column " + macroCol;
        }
    }

    public AST deepCopy() {
        AST result = new AST();

        copyCommonASTFields(result);

        return result;
    }

    void copyCommonASTFields(AST ast) {
        ast.col = this.col;
        ast.line = this.line;
        ast.lbl = this.lbl;
        ast.lblLocation = this.lblLocation;
        ast.macroLine = this.macroLine;
        ast.macroOriginBegin = this.macroOriginBegin;
        ast.macroOriginEnd = this.macroOriginEnd;
        ast.setOrigin(this.getOrigin());
    }

    /**
     * Calls the deepCopy() method of each AST object in the vector and returns the results in a new vector.
     *
     * @param vector the vector to be copied
     * @return the resulting vector from calling each object's deepCopy() method
     */
    private static Vector deepCopyVectorOfAST(Vector vector) {
        Vector result = new Vector();
        for (int i = 0; i <= vector.size() - 1; i++) {
            result.addElement(((AST) (vector.get(i))).deepCopy());
        }
        return result;
    }

    private static Vector deepCopyTLAExprs(Vector exprs) {
        Vector result = new Vector();

        for (int i = 0; i <= exprs.size() - 1; i++) {
            TLAExpr element = (TLAExpr) exprs.get(i);
            result.addElement(element.cloneAndNormalize());
        }
        return result;
    }

    private static Vector deepCopyVectorOfVectorsOfAST(Vector vector) {
        Vector res = new Vector();
        for (int i = 0; i <= vector.size() - 1; i++) {
            Vector element = (Vector) vector.get(i);
            res.add(deepCopyVectorOfAST(element));
        }
        return res;
    }

    /**
     * Creates an "either stmt or skip" statement.
     * @param stmt The statement, which should be present in the "either" block
     * @return The created either object
     */
    protected Either CreateEitherStmtOrSkip(AST stmt) {
        AST.Either result = new AST.Either();
        result.line = line;
        result.col = col;
        result.setOrigin(this.getOrigin());

        Vector stmtVec = new Vector();
        stmtVec.addElement(stmt);
        AST.Skip skip = new AST.Skip();
        Vector skipVec = new Vector();
        skipVec.addElement(skip);

        result.ors = new Vector();
        result.ors.addElement(stmtVec);
        result.ors.addElement(skipVec);

        return result;
    }

    public static void ASTInit()
    /*********************************************************************
     * An initializing method that creates the ...Obj objects used to     *
     * test the class of an AST object.                                   *
     *********************************************************************/
    {
        UniprocessObj = new AST.Uniprocess();
        MultiprocessObj = new AST.Multiprocess();
        ProcedureObj = new AST.Procedure();
        ProcessObj = new AST.Process();
        VarDeclObj = new AST.VarDecl();
        PVarDeclObj = new AST.PVarDecl();
        LabeledStmtObj = new AST.LabeledStmt();
        WhileObj = new AST.While();
        AssignObj = new AST.Assign();
        SingleAssignObj = new AST.SingleAssign();
        LhsObj = new AST.Lhs();
        IfObj = new AST.If();
        EitherObj = new AST.Either();
        WithObj = new AST.With();
        WhenObj = new AST.When();
        PrintSObj = new AST.PrintS();
        AssertObj = new AST.Assert();
        SkipObj = new AST.Skip();
        LabelIfObj = new AST.LabelIf();
        LabelEitherObj = new AST.LabelEither();
        CallObj = new AST.Call();
        ReturnObj = new AST.Return();
        CallReturnObj = new AST.CallReturn();
        CallGotoObj = new AST.CallGoto();
        GotoObj = new AST.Goto();
        MacroObj = new AST.Macro();
        MacroCallObj = new AST.MacroCall();
        SendCallObj = new AST.SendCall();
        ReceiveCallObj = new AST.ReceiveCall();
        GetAllProcsCallObj = new AST.GetAllProcsCall();
        FailObj = new AST.Fail();
        MaybeFailObj = new AST.MaybeFail();
    }


    public static class Uniprocess extends AST {
        public String name = "";
        public Vector decls = null; // of VarDecl
        public TLAExpr defs = null;
        public Vector macros = null; // of Macro
        public Vector prcds = null; // of Procedure
        public Vector body = null; // of LabeledStmt

        public Uniprocess() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type     |-> \"uniprocess\", " + NewLine() +
                            " name  |-> \"" + name + "\", " + NewLine() +
                            Indent(" decls  |-> ") + VectorToSeqString(decls) + ","
                            +
                            EndIndent() + NewLine() +
                            Indent(" defs   |-> ") + defs.toString() + ","
                            +
                            EndIndent() + NewLine() +

                            /*************************************************************
                             * Uncomment the following to print the macros field.  It is  *
                             * commented out so the printed result is what PlusCal.tla    *
                             * considers a Uniprocess object to be.                       *
                             *************************************************************/
                            // Indent(" macros |-> ") + VectorToSeqString(macros) + ","
                            //                             +
                            //  EndIndent() + NewLine() +

                            Indent(" prcds  |-> ") + VectorToSeqString(prcds) + ","
                            +
                            EndIndent() + NewLine() +
                            Indent(" body  |-> ") + VectorToSeqString(body) + "]" +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public Uniprocess deepCopy() {
            Uniprocess result = new Uniprocess();

            copyCommonASTFields(result);

            result.name = this.name;
            result.body = deepCopyVectorOfAST(this.body);
            result.prcds = deepCopyVectorOfAST(this.prcds);
            result.prcds = deepCopyVectorOfAST(this.prcds);
            result.decls = deepCopyVectorOfAST(this.decls);
            result.defs = this.defs.cloneAndNormalize();
            result.macros = deepCopyVectorOfAST(this.macros);

            return result;
        }

    }

    public static class Multiprocess extends AST {
        public String name = "";
        public Vector decls = null; // of VarDecl
        public TLAExpr defs = null;
        public Vector macros = null; // of Macro
        public Vector prcds = null; // of Procedure
        public Vector procs = null; // of Process

        public Multiprocess() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type    |-> \"multiprocess\", " + NewLine() +
                            " name  |-> \"" + name + "\", " + NewLine() +
                            Indent(" decls |-> ") + VectorToSeqString(decls) + ","
                            +
                            EndIndent() + NewLine() +
                            Indent(" defs  |-> ") + defs.toString() + ","
                            +
                            EndIndent() + NewLine() +
                            /*************************************************************
                             * Uncomment the following to print the macros field.  It is  *
                             * commented out so the printed result is what PlusCal.tla    *
                             * considers a Multiprocess object to be.                     *
                             *************************************************************/
                            // Indent(" macros |-> ") + VectorToSeqString(macros) + ","
                            //                             +
                            // EndIndent() + NewLine() +

                            Indent(" prcds |-> ") + VectorToSeqString(prcds) + ","
                            +
                            EndIndent() + NewLine() +
                            Indent(" procs |-> ") + VectorToSeqString(procs) + "]" +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public Multiprocess deepCopy() {
            Multiprocess result = new Multiprocess();

            copyCommonASTFields(result);

            result.name = this.name;
            result.decls = deepCopyVectorOfAST(this.decls);
            result.defs = this.defs.cloneAndNormalize();
            result.macros = deepCopyVectorOfAST(this.macros);
            result.prcds = deepCopyVectorOfAST(this.prcds);
            result.procs = deepCopyVectorOfAST(this.procs);

            return result;
        }

    }

    /**
     * The minusLabels and plusLabels fields were added by LL in
     * January 2011 to implement the Version 1.5 enhancement that allows
     * fairness modifiers on labels.  These Vectors contain the labels
     * in the process that have the indicated modifier.  They are initially
     * set in the GetProcedure method of ParseAlgorithm, with the help of
     * the GetLabel method.  They are then fixed to correct for label
     * conflicts by the FixProcedure method of PcalFixIDs.
     * <p>
     * The proceduresCalled field was added later in Jan 2011 by LL because,
     * since procedures can call other procedures, a transitive closure
     * is required to compute the procedures called by a process.  (Those
     * procedures need to be known to compute the fairness conditions, since
     * a fairness requirement on a process implies a fairness requirement on
     * all the procedures that the process calls.)
     * <p>
     * Note added 2 Apr 2013 by LL.  Also, it should be noted
     * that the transitive closure is computed by the call to PcalFixIDs.Fix,
     * not during the initial parsing phase.
     *
     * @author lamport
     */
    public static class Procedure extends AST {
        public String name = "";
        public Vector minusLabels = new Vector();
        public Vector plusLabels = new Vector();
        public Vector proceduresCalled = new Vector();
        public Vector params = null; // of PVarDecl
        public Vector decls = null; // of PVarDecl
        public Vector body = null; // of LabeledStmt

        public Procedure() {
        }

        ;

        public String toString() {
            // For versions earlier than 1.5 need to return those versions'
            // value since toString() is used to generate the AST module
            // used when TLC is doing the translation.
            if (PcalParams.inputVersionNumber < PcalParams.VersionToNumber("1.5")) {
                return
                        Indent(lineCol()) +
                                "[name   |-> \"" + name + "\", " + NewLine() +
                                Indent(" params |-> ") + VectorToSeqString(params) + "," +
                                EndIndent() + NewLine() +
                                Indent(" decls  |-> ") + VectorToSeqString(decls) + "," +
                                EndIndent() + NewLine() +
                                Indent(" body   |-> ") + VectorToSeqString(body) + "]" +
                                EndIndent() +
                                EndIndent();
            }
            return
                    Indent(lineCol()) +
                            "[name   |-> \"" + name + "\", " + NewLine() +
                            "minusLabels |-> "
                            + VectorToSeqQuotedString(minusLabels) + ", plusLabels |->"
                            + VectorToSeqQuotedString(plusLabels) + ", proceduresCalled |->"
                            + VectorToSeqQuotedString(proceduresCalled) + ","
                            + NewLine() +
                            Indent(" params |-> ") + VectorToSeqString(params) + "," +
                            EndIndent() + NewLine() +
                            Indent(" decls  |-> ") + VectorToSeqString(decls) + "," +
                            EndIndent() + NewLine() +
                            Indent(" body   |-> ") + VectorToSeqString(body) + "]" +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public Procedure deepCopy() {
            Procedure res = new Procedure();

            copyCommonASTFields(res);

            res.name = this.name;
            res.body = deepCopyVectorOfAST(this.body);
            res.params = deepCopyVectorOfAST(this.params);
            res.decls = deepCopyVectorOfAST(this.decls);
            res.minusLabels = new Vector(this.minusLabels); // vector of strings, so this should be ok
            res.plusLabels = new Vector(this.plusLabels); // vector of strings, so this should be ok
            res.proceduresCalled = new Vector(this.proceduresCalled); // vector of strings, so this should be ok

            return res;
        }
    }

    /***********************************************************************
     * Constants used to describe a process's fairness assumption.          *
     ***********************************************************************/
    public static final int UNFAIR_PROC = 0;
    public static final int WF_PROC = 1;
    public static final int SF_PROC = 2;
    public static final String[] FairnessString = {"unfair", "wf", "sf"};

    /**
     * The minusLabels and plusLabels fields were added by LL in
     * January 2011 to implement the Version 1.5 enhancement that allows
     * fairness modifiers on labels.  They are set much like the corresponding
     * fields of an AST.Procedure object, as described above.
     * The proceduresCalled field was also added then.
     * <p>
     * Note added by LL on 2 April 2013.  The genius LL never noticed that
     * the proceduresCalled field only contains the procedures directly called,
     * and he used that in generating the fairness conditions without finding
     * the procedures that are called indirectly.
     *
     * @author lamport
     */
    public static class Process extends AST {
        public String name = "";
        public int fairness = UNFAIR_PROC;
        public Vector minusLabels = new Vector();
        public Vector plusLabels = new Vector();
        public Vector proceduresCalled = new Vector();
        public boolean isEq = true; // true means "=", false means "\\in"
        public TLAExpr id = null;
        public Vector decls = null; // of VarDecl
        public Vector body = null; // of LabeledStmt

        public Process() {
        }

        ;

        public String toString() {
            // For versions earlier than 1.5 need to return those versions'
            // value since toString() is used to generate the AST module
            // used when TLC is doing the translation.
            if (PcalParams.inputVersionNumber < PcalParams.VersionToNumber("1.5")) {
                return
                        Indent(lineCol()) +
                                "[name   |-> \"" + name + "\", " + NewLine() +
                                " eqOrIn |-> " + boolToEqOrIn(isEq) + "," + NewLine() +
                                " id     |-> " + id.toString() + "," + NewLine() +
                                Indent(" decls  |-> ") +
                                VectorToSeqString(decls) + "," +
                                EndIndent() + NewLine() +
                                Indent(" body   |-> ") +
                                VectorToSeqString(body) + "]" +
                                EndIndent() +
                                EndIndent();
            }

            return
                    Indent(lineCol()) +
                            "[name   |-> \"" + name + "\","
                            + NewLine() +
                            " fairness |-> \""
                            + FairnessString[fairness] + "\", minusLabels |-> "
                            + VectorToSeqQuotedString(minusLabels) + ", plusLabels |->"
                            + VectorToSeqQuotedString(plusLabels) + ", proceduresCalled |->"
                            + VectorToSeqQuotedString(proceduresCalled) + ","
                            + NewLine() +
                            " eqOrIn |-> " + boolToEqOrIn(isEq) + "," + NewLine() +
                            " id     |-> " + id.toString() + "," + NewLine() +
                            Indent(" decls  |-> ") +
                            VectorToSeqString(decls) + "," +
                            EndIndent() + NewLine() +
                            Indent(" body   |-> ") +
                            VectorToSeqString(body) + "]" +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public Process deepCopy() {
            Process result = new Process();

            copyCommonASTFields(result);

            result.name = this.name;
            result.minusLabels = new Vector(minusLabels);
            result.plusLabels = new Vector(plusLabels);
            result.proceduresCalled = new Vector(proceduresCalled);
            result.isEq = this.isEq;
            result.id = this.id.cloneAndNormalize();
            result.decls = deepCopyVectorOfAST(decls);
            result.body = deepCopyVectorOfAST(body);

            return result;
        }
    }

    public static class VarDecl extends AST {
        public String var = null;
        public boolean isEq = true; // true means "=", false means "\\in"
        public TLAExpr val = PcalParams.DefaultVarInit();

        public VarDecl() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[var |-> \"" + var + "\", " +
                            "eqOrIn |-> " + boolToEqOrIn(isEq) + ", " +
                            "val |-> " + val.toString() + "]" +
                            EndIndent();
        }

        @Override
        public VarDecl deepCopy() {
            VarDecl result = new VarDecl();

            copyCommonASTFields(result);

            result.var = this.var;
            result.isEq = this.isEq;
            result.val = this.val.cloneAndNormalize();

            return result;
        }
    }

    public static class PVarDecl extends AST {
        public final boolean isEq = true;  // true means "="
        public String var = null;
        public TLAExpr val = PcalParams.DefaultVarInit();

        public PVarDecl() {
        }

        ;

        /**
         * Converts the PVarDecl object to an equivalent VarDecl
         * object.  (I don't know why I bothered introducing a separate
         * PVarDecl object in the first place.)
         *
         * @return
         */
        public VarDecl toVarDecl() {
            VarDecl result = new VarDecl();
            result.var = this.var;
            result.val = this.val;
            result.setOrigin(this.getOrigin());
            result.isEq = true;
            return result;
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[var |-> \"" + var + "\", " +
                            "eqOrIn |-> \"=\", " +
                            "val |-> " + val.toString() + "]" +
                            EndIndent();
        }

        @Override
        public PVarDecl deepCopy() {
            PVarDecl result = new PVarDecl();

            copyCommonASTFields(result);

            result.var = this.var;
            result.val = this.val.cloneAndNormalize();

            return result;
        }
    }

    public static class LabeledStmt extends AST {
        public String label = null;
        public Vector stmts = null;

        /*****************************************************************
         * An optional While prepended to a LabelSeq.                     *
         *****************************************************************/

        public LabeledStmt() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[label |-> \"" + label + "\"," + NewLine() +
                            Indent(" stmts |-> ") +
                            VectorToSeqString(stmts) + "]" +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public LabeledStmt deepCopy() {
            LabeledStmt result = new LabeledStmt();

            copyCommonASTFields(result);

            result.label = this.label;
            result.stmts = deepCopyVectorOfAST(stmts);

            return result;
        }
    }


    public static class While extends AST {
        public TLAExpr test = null;
        public Vector unlabDo = null; // a LabelSeq
        public Vector labDo = null; // of LabeledStmt

        public While() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type    |-> \"while\", " + NewLine() +
                            " test    |-> " + test.toString() + "," + NewLine() +
                            Indent(" labDo   |-> ") +
                            VectorToSeqString(labDo) + "," +
                            EndIndent() + NewLine() +

                            Indent(" unlabDo |-> ") +
                            VectorToSeqString(unlabDo) + "]" +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public While deepCopy() {
            While result = new While();

            copyCommonASTFields(result);

            result.test = this.test.cloneAndNormalize();
            result.labDo = deepCopyVectorOfAST(this.labDo);
            result.unlabDo = deepCopyVectorOfAST(this.unlabDo);

            return result;
        }

    }


    public static class Assign extends AST {
        public Vector ass = null; // of SingleAssign

        public Assign() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type |-> \"assignment\"," + NewLine() +
                            Indent(" ass  |-> ") +
                            VectorToSeqString(ass) + "]" +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public Assign deepCopy() {
            Assign result = new Assign();

            copyCommonASTFields(result);

            result.ass = deepCopyVectorOfAST(this.ass);

            return result;
        }
    }

    public static class SingleAssign extends AST {
        public Lhs lhs = new Lhs();
        public TLAExpr rhs = null;

        public SingleAssign() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[lhs |-> " + lhs.toString() + "," + NewLine() +
                            " rhs |-> " + rhs.toString() + "]" +
                            EndIndent();
        }

        @Override
        public SingleAssign deepCopy() {
            SingleAssign result = new SingleAssign();

            copyCommonASTFields(result);

            result.lhs = this.lhs.deepCopy();
            result.rhs = this.rhs.cloneAndNormalize();

            return result;
        }
    }

    public static class Lhs extends AST
            /*********************************************************************
             * Note use of Lhs as name rather than LHS, which is the type         *
             * constant.                                                          *
             *********************************************************************/
    {
        public String var = "";
        public TLAExpr sub = null;

        public Lhs() {
        }

        ;

        public String toString() {
            return lineCol() +
                    "[var |-> \"" + var + "\", sub |-> "
                    + sub.toString() + "]";
        }

        @Override
        public Lhs deepCopy() {
            Lhs result = new Lhs();

            copyCommonASTFields(result);

            result.var = this.var;
            result.sub = this.sub.cloneAndNormalize();

            return result;
        }
    }

    /**
     * An AST.If object is created from an AST.LabelIf or AST.While object.
     * For a LabelIf containing no labeled statements, it is created inside
     * the CheckLabeledStmtSeq method when executing ParseAlgorithm.runMe(String[]).
     * Otherwise, it is created by exploding the original AST inside the
     * call of  PcalFixIDs.Fix.  Its origin is set to that of the original AST.
     *
     * @author lamport
     */
    public static class If extends AST {
        public TLAExpr test = null;
        public Vector Then = null; // of SimpleStmt
        /*****************************************************************
         * Could use "then", but use "Then" to avoid confusion since we   *
         * can't use "else".                                              *
         *****************************************************************/
        public Vector Else = null; // of SimpleStmt
        /*****************************************************************
         * Can't use "else" because that's a Java keyword.                *
         *****************************************************************/

        public static final int UNBROKEN = 0;
        public static final int BROKEN_WHILE = 1;
        public static final int BROKEN_THEN = 2;
        public static final int BROKEN_ELSE = 4;
        /**
         * The source field records the information about where the If came
         * from that is useful for the TLA+ to PlusCal translation.  The values
         * are:
         * <p>
         * UNBROKEN : Contains the entire contents of the original AST.
         * BROKEN_WHILE : Came from a While containing a labeled statement.
         * BROKEN_THEN : Came from an IfThen that contained a labeled statement
         * in the Then clause, but not the Else clausew.
         * BROKEN_ELSE : Came from an IfThen that contained a labeled statement
         * in the Else clause but not the Then clause.
         * BROKEN_THEN + BROKEN_ELSE : Came from an IfThen with labeled statements
         * in both clauses.
         */
        private int source = UNBROKEN;

        public int getSource() {
            return source;
        }

        public void setSource(int source) {
            this.source = source;
        }

        public If() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type    |-> \"if\", " + NewLine() +
                            " test    |-> " + test.toString() + "," + NewLine() +
                            Indent(" then |-> ") + VectorToSeqString(Then) + ","
                            +
                            EndIndent() + NewLine() +
                            Indent(" else |-> ") + VectorToSeqString(Else) + "]" +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public If deepCopy() {
            If result = new If();

            copyCommonASTFields(result);

            result.test = this.test.cloneAndNormalize();
            result.Then = deepCopyVectorOfAST(this.Then);
            result.Else = deepCopyVectorOfAST(this.Else);

            return result;
        }
    }

    public static class Either extends AST {
        public Vector ors = null; // of Seq(public Vector getStmts())

        public Either() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type |-> \"either\", " + NewLine() +
                            Indent(" ors  |-> ") + VectorOfVectorsToSeqString(ors) + "]" +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public Either deepCopy() {
            Either result = new Either();

            copyCommonASTFields(result);

            result.ors = deepCopyVectorOfVectorsOfAST(this.ors);

            return result;
        }

    }

    public static class With extends AST {
        public String var = "";
        public boolean isEq = true; // true means "=", false "\\in"
        public TLAExpr exp = null;
        public Vector Do = null; // of SimpleStmt

        /*****************************************************************
         * Can't use "do" because that's a Java keyword.                  *
         *****************************************************************/
        public With() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type   |-> \"with\", " + NewLine() +
                            " var    |-> \"" + var + "\"," + NewLine() +
                            " eqOrIn |-> " + boolToEqOrIn(isEq) + "," + NewLine() +
                            " exp    |-> " + exp.toString() + "," + NewLine() +
                            Indent(" do     |-> ") + VectorToSeqString(Do) + "]" +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public With deepCopy() {
            With result = new With();

            copyCommonASTFields(result);

            result.var = this.var;
            result.isEq = this.isEq;
            result.exp = this.exp.cloneAndNormalize();
            result.Do = deepCopyVectorOfAST(this.Do);

            return result;
        }

    }

    public static class When extends AST {
        public TLAExpr exp = null;

        public When() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type |-> \"when\", " + NewLine() +
                            " exp |-> " + exp.toString() + "]" +
                            EndIndent();
        }

        @Override
        public When deepCopy() {
            When result = new When();

            copyCommonASTFields(result);

            result.exp = this.exp.cloneAndNormalize();

            return result;
        }
    }

    public static class PrintS extends AST {
        public TLAExpr exp = null;

        public PrintS() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type |-> \"print\", " + NewLine() +
                            " exp |-> " + exp.toString() + "]" +
                            EndIndent();
        }

        @Override
        public PrintS deepCopy() {
            PrintS result = new PrintS();

            copyCommonASTFields(result);

            result.exp = this.exp.cloneAndNormalize();

            return result;
        }
    }

    public static class Assert extends AST {
        public TLAExpr exp = null;

        public Assert() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type |-> \"assert\", " + NewLine() +
                            " exp |-> " + exp.toString() + "]" +
                            EndIndent();
        }

        @Override
        public Assert deepCopy() {
            Assert result = new Assert();

            copyCommonASTFields(result);

            result.exp = this.exp.cloneAndNormalize();

            return result;
        }
    }

    public static class Skip extends AST {
        public Skip() {
        }

        ;

        public String toString() {
            return lineCol() + "[type |-> \"skip\"]";
        }

        @Override
        public Skip deepCopy() {
            Skip result = new Skip();

            copyCommonASTFields(result);

            return result;
        }
    }


    /**
     * A LabelIf represents an if statement whose then and/or
     * else clause has a label.
     *
     * @author lamport
     */
    public static class LabelIf extends AST {
        public TLAExpr test = null;
        public Vector unlabThen = null; // a LabelSeq
        public Vector labThen = null; // of LabeledStmt
        public Vector unlabElse = null; // a LabelSeq
        public Vector labElse = null; // of LabeledStmt

        public LabelIf() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type      |-> \"labelIf\"," + NewLine() +
                            " test      |-> " + test.toString() + "," + NewLine() +
                            Indent(" unlabThen |-> ") + VectorToSeqString(unlabThen)
                            + "," +
                            EndIndent() + NewLine() +
                            Indent(" labThen   |-> ") + VectorToSeqString(labThen)
                            + "," +
                            EndIndent() + NewLine() +
                            Indent(" unlabElse |-> ") + VectorToSeqString(unlabElse)
                            + "," +
                            EndIndent() + NewLine() +
                            Indent(" labElse   |-> ") + VectorToSeqString(labElse)
                            + "]" +
                            EndIndent() + NewLine() +
                            EndIndent();
        }

        @Override
        public LabelIf deepCopy() {
            LabelIf result = new LabelIf();

            copyCommonASTFields(result);

            result.test = this.test.cloneAndNormalize();
            result.unlabThen = deepCopyVectorOfAST(unlabThen);
            result.labThen = deepCopyVectorOfAST(labThen);
            result.unlabElse = deepCopyVectorOfAST(unlabElse);
            result.labElse = deepCopyVectorOfAST(labElse);

            return result;
        }
    }

    public static class LabelEither extends AST {
        public Vector clauses = null; // of Clause

        public LabelEither() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type    |-> \"labelEither\"," + NewLine() +
                            Indent(" clauses |-> ") + VectorToSeqString(clauses)
                            + "]" +
                            EndIndent() + NewLine() +
                            EndIndent();
        }

        @Override
        public LabelEither deepCopy() {
            LabelEither result = new LabelEither();

            copyCommonASTFields(result);

            result.clauses = deepCopyVectorOfAST(this.clauses);

            return result;
        }

    }

    public static class Clause extends AST {
        public Vector unlabOr = null; // a LabelSeq
        public Vector labOr = null; // LabeledStmt

        public Clause() {
        }

        /**
         * The broken field is true iff the Clause object came from
         * a LabelEither object for which the corresponding clause
         * contained a labeled statement.
         */
        private boolean broken = false;

        public boolean isBroken() {
            return broken;
        }

        public void setBroken(boolean broken) {
            this.broken = broken;
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            Indent("[unlabOr |-> ") + VectorToSeqString(unlabOr)
                            + "," +
                            EndIndent() + NewLine() +
                            Indent(" labOr   |-> ") + VectorToSeqString(labOr)
                            + "]" +
                            EndIndent() + NewLine() +
                            EndIndent();
        }

        @Override
        public Clause deepCopy() {
            Clause result = new Clause();

            copyCommonASTFields(result);

            result.unlabOr = deepCopyVectorOfAST(this.unlabOr);
            result.labOr = deepCopyVectorOfAST(this.labOr);

            return result;
        }
    }

    public static class Call extends AST {
        public String returnTo = "";
        public String to = "";
        public Vector args = null; // of TLAExpr

        public Call() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type     |-> \"call\"," + NewLine() +
                            " returnTo |-> \"" + returnTo + "\"," + NewLine() +
                            " to       |-> \"" + to + "\"," + NewLine() +
                            Indent(" args     |-> ") + VectorToSeqString(args) + "]" +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public Call deepCopy() {
            Call result = new Call();

            copyCommonASTFields(result);

            result.returnTo = this.returnTo;
            result.to = this.to;
            result.args = deepCopyTLAExprs(args);

            return result;
        }
    }

    public static class Return extends AST {
        public String from = "";

        public Return() {
        }

        ;

        public String toString() {
            return
                    lineCol() +
                            "[type |-> \"return\", from |-> \"" + from + "\"]";
        }

        @Override
        public Return deepCopy() {
            Return result = new Return();

            copyCommonASTFields(result);

            result.from = this.from;

            return result;
        }
    }

    /**
     * A CallReturn object represents a call immediately followed
     * by a return.
     *
     * @author lamport
     */
    public static class CallReturn extends AST {
        public String from = "";
        public String to = "";
        public Vector args = null; // of TLAExpr

        public CallReturn() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type     |-> \"callReturn\"," + NewLine() +
                            " from     |-> \"" + from + "\"," + NewLine() +
                            " to       |-> \"" + to + "\"," + NewLine() +
                            Indent("args     |-> ") + VectorToSeqString(args)
                            + "]" + NewLine() +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public CallReturn deepCopy() {
            CallReturn result = new CallReturn();

            copyCommonASTFields(result);

            result.from = this.from;
            result.to = this.to;
            result.args = deepCopyTLAExprs(args);

            return result;
        }
    }

    public static class CallGoto extends AST {
        public String after = "";
        public String to = "";
        public Vector args = null; // of TLAExpr

        public CallGoto() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type     |-> \"callGoto\"," + NewLine() +
                            " after    |-> \"" + after + "\"," + NewLine() +
                            " to       |-> \"" + to + "\"," + NewLine() +
                            Indent("args     |-> ") + VectorToSeqString(args)
                            + "]" + NewLine() +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public CallGoto deepCopy() {
            CallGoto result = new CallGoto();

            copyCommonASTFields(result);

            result.after = this.after;
            result.to = this.to;
            result.args = AST.deepCopyTLAExprs(args);

            return result;
        }
    }

    public static class Goto extends AST {
        public String to = "";

        public Goto() {
        }

        ;

        public String toString() {
            return
                    lineCol() +
                            "[type |-> \"goto\", " +
                            " to |-> \"" + to + "\"]";
        }

        @Override
        public Goto deepCopy() {
            Goto result = new Goto();

            copyCommonASTFields(result);

            result.to = this.to;

            return result;
        }
    }

    public static class Macro extends AST {
        public String name = "";
        public Vector params = null; // of Strings
        public Vector body = null; // of Stmt

        public Macro() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[name   |-> \"" + name + "\", " + NewLine() +
                            Indent(" params |-> ") + VectorToSeqString(params) + "," +
                            EndIndent() + NewLine() +
                            Indent(" body   |-> ") + VectorToSeqString(body) + "]" +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public Macro deepCopy() {
            Macro result = new Macro();

            copyCommonASTFields(result);

            result.name = this.name;
            result.params = new Vector(params);
            result.body = AST.deepCopyVectorOfAST(body);

            return result;
        }
    }

    public static class MacroCall extends AST {
        public String name = "";
        public Vector args = null; // of TLAExpr

        public MacroCall() {
        }

        ;

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[type |-> \"macrocall\"," + NewLine() +
                            " name |-> \"" + name + "\"," + NewLine() +
                            Indent(" args     |-> ") + VectorToSeqString(args) + "]" +
                            EndIndent() +
                            EndIndent();
        }

        @Override
        public MacroCall deepCopy() {
            MacroCall result = new MacroCall();

            copyCommonASTFields(result);

            result.name = this.name;
            result.args = AST.deepCopyTLAExprs(args);

            return result;
        }
    }

    /***************************** UTILITY METHODS ****************************/

    public String boolToEqOrIn(boolean iseq) {
        if (iseq) {
            return "\"=\"";
        } else {
            return "\"\\\\in\"";
        }
    }

    public String lineCol()
    /**********************************************************************
     * Equals "(*line, col*)" if pcal.trans called in debugging mode,      *
     * otherwise the empty string.                                         *
     **********************************************************************/
    {
        if (PcalParams.Debug) {
            return "(*" + line + ", " + col + "*)";
        } else {
            return "";
        }
    }

    /************************************************************************
     * Methods for getting the toString() methods to indent the              *
     * representation nicely so it's readable.  They are used as follows.    *
     * Suppose we are printing a record with fields foo, foobar, elf, and    *
     * we want it to be output as:                                           *
     *                                                                       *
     *    [foo |-> XXXXXX                                                    *
     *             XXXXXX                                                    *
     *             XXXXX ,                                                   *
     *     elf    |-> "elf",                                                 *
     *     foobar |-> YYYY                                                   *
     *                YYY ]                                                  *
     *                                                                       *
     * where XX...XXX is produced by XXX.toString and YY...YYY by            *
     * YYY.toString().  We would produce the string as follows:              *
     *                                                                       *
     *    Indent("[foo |-> ") +                                              *
     *           XXX.toString() + "," +                                      *
     *    EndIndent() + NewLine() +                                          *
     *    "[elf    |-> \"elf\"," + NewLine()                                 *
     *    NewLine() +                                                        *
     *    Indent(" foobar |-> ") +                                           *
     *             XXX.toString() + "]" +                                    *
     *    EndIndent()                                                        *
     ************************************************************************/
    public static int indentDepth = 0;
    public static int[] curIndent = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};

    /**********************************************************************
     * There must be an easier way.                                        *
     **********************************************************************/

    public static String Indent(String str) {
        curIndent[indentDepth + 1] = curIndent[indentDepth] + str.length();
        indentDepth = indentDepth + 1;
        return str;
    }

    public static String EndIndent() {
        indentDepth = indentDepth - 1;
        return "";
    }


    public static String NewLine() {
        String result = "\n";
        int i = 0;
        while (i < curIndent[indentDepth]) {
            result = result + " ";
            i = i + 1;
        }
        ;
        return result;
    }


    public static String VectorToSeqString(Vector vec)
    /**********************************************************************
     * Returns the TLA+ representation of vec as a sequence of its         *
     * elements, where toString() is used to produce the elements'         *
     * representation.                                                     *
     **********************************************************************/
    {
        if (vec == null) {
            return "null";
        }
        ;
        String result = Indent("<<");
        int i = 0;
        while (i < vec.size()) {
            if (i > 0) {
                result = result + ", " + NewLine();
            }
            ;
            result = result + vec.elementAt(i).toString();
            i = i + 1;
        }
        ;
        return result + ">>" + EndIndent();
    }

    public static String VectorToSeqQuotedString(Vector vec)
    /**********************************************************************
     * Returns the TLA+ representation of vec as a sequence of quoted      *
     * elements, where toString() is used to produce the elements'         *
     * representation to be quoted.                                        *
     **********************************************************************/
    {
        if (vec == null) {
            return "null";
        }
        ;
        String result = Indent("<<");
        int i = 0;
        while (i < vec.size()) {
            if (i > 0) {
                result = result + ", " /* + NewLine() */;
            }
            ;
            result = result + "\"" + vec.elementAt(i).toString() + "\"";
            i = i + 1;
        }
        ;
        return result + ">>" + EndIndent();
    }

    public static String VectorOfVectorsToSeqString(Vector vecvec)
    /**********************************************************************
     * Returns the TLA+ representation of vec as a sequence of its         *
     * elements, where each of its elements is a vector of objects whose   *
     * representation is obtained by calling toString().                   *
     **********************************************************************/
    {
        String result = Indent("<< ");
        int i = 0;
        while (i < vecvec.size()) {
            if (i > 0) {
                result = result + ", " + NewLine();
            }
            ;
            result = result + VectorToSeqString((Vector) vecvec.elementAt(i));
            i = i + 1;
        }
        ;
        return result + " >>" + EndIndent();
    }

    public static class SendCall extends AST {
        public PCalErlangConstants.SendType type;
        public TLAExpr receiver = new TLAExpr(new Vector());
        public TLAExpr message = null;
        public String queuesName = PCalErlangConstants.GLOBAL_QUEUES_NAME; // read-only, global message queue name

        public SendCall() {
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[SendCall:" + NewLine() +
                            " type |-> \"" + type.toString() + "\"," + NewLine() +
                            Indent(" channel |-> ") + getQueuesName() +
                            EndIndent() + NewLine() +
                            Indent(" callExp |-> ") + receiver +
                            EndIndent() + NewLine() +
                            Indent(" msg |-> ") + message + "]" +
                            EndIndent();
        }

        @Override
        public SendCall deepCopy() {
            SendCall result = new SendCall();

            copyCommonASTFields(result);

            result.type = this.type;
            result.receiver = this.receiver.cloneAndNormalize();
            result.message = this.message.cloneAndNormalize();
            result.queuesName = this.queuesName;

            return result;
        }

        public String getQueuesName() {
            return queuesName;
        }

        public Vector getStmts() throws TLAExprException, ParseAlgorithmException {

            if (this.type == PCalErlangConstants.SendType.SEND) {
                return getTypeSendStmts();
            } else if (this.type == PCalErlangConstants.SendType.BROADCAST) {
                return getTypeBroadcastStmts();
            } else {
                throw new ParseAlgorithmException("Encountered unknown send type"); // todo: probably good to change exception type here
            }
        }

        private Vector getTypeBroadcastStmts() {
            String queuesName = this.getQueuesName();

            AST.SingleAssign sass = new AST.SingleAssign();
            sass.line = line;
            sass.col = col;
            sass.lhs.var = queuesName;
            sass.lhs.sub = new TLAExpr();

            TLAExpr rightExpr = new TLAExpr();
            String proc = "erla_proc";
            rightExpr.addLine();
            rightExpr.addToken(PcalTranslate.BuiltInToken("["));
            rightExpr.addToken(PcalTranslate.IdentToken(proc));
            rightExpr.addToken(PcalTranslate.BuiltInToken(" \\in"));
            rightExpr.addToken(PcalTranslate.BuiltInToken(" DOMAIN "));
            rightExpr.addToken(PcalTranslate.IdentToken(PCalErlangConstants.GLOBAL_QUEUES_NAME));
            rightExpr.addToken(PcalTranslate.BuiltInToken(" |->"));
            rightExpr.addToken(PcalTranslate.BuiltInToken(" Append"));
            rightExpr.addToken(PcalTranslate.BuiltInToken("("));
            rightExpr.addToken(PcalTranslate.IdentToken(PCalErlangConstants.GLOBAL_QUEUES_NAME));
            rightExpr.addToken(PcalTranslate.BuiltInToken("["));
            rightExpr.addToken(PcalTranslate.IdentToken(proc));
            rightExpr.addToken(PcalTranslate.BuiltInToken("]"));
            addMessageTokens(rightExpr);
            rightExpr.addToken(PcalTranslate.BuiltInToken("]"));

            rightExpr.normalize();

            sass.rhs = rightExpr;
            sass.setOrigin(this.getOrigin());

            AST.Assign assign = new AST.Assign();
            assign.ass = new Vector();
            assign.line = line;
            assign.col = col;
            assign.setOrigin(this.getOrigin());

            assign.ass.addElement(sass);

            // create "either or" to model an unreliable network
            AST.Either either = CreateEitherStmtOrSkip(assign);

            Vector result = new Vector();
            result.addElement(either);

            return result;
        }

        private void addMessageTokens(TLAExpr rightExpr) {
            rightExpr.addToken(PcalTranslate.BuiltInToken(", "));
            // add message
            for (int i = 0; i < this.message.tokens.size(); i++) {
                Vector tv = (Vector) this.message.tokens.elementAt(i);
                for (int j = 0; j < tv.size(); j++) {
                    TLAToken tok = (TLAToken) tv.elementAt(j);
                    rightExpr.addToken(tok);
                }
            }
            rightExpr.addToken(PcalTranslate.BuiltInToken(")"));
        }

        private Vector getTypeSendStmts() throws TLAExprException {
            /**
             * Get the following statement:
             *
             *  either
             *    queues[proc] := Append(queues[proc], message)
             *  or
             *    skip;
             *  end either;
             *
             *  If at some point one wants to generate code for a reliable network semantics, then
             *    just remove the "either" object and add the AST.Sssign statement to the result vector instead.
             */

            String queuesName = this.getQueuesName();

            AST.SingleAssign sass = new AST.SingleAssign();
            sass.line = line;
            sass.col = col;
            sass.lhs.var = this.queuesName;

            TLAExpr recWithBrackets;
            if (receiver.tokens != null) {
                recWithBrackets = new TLAExpr();
                recWithBrackets.addLine();
                recWithBrackets.addToken(PcalTranslate.BuiltInToken("["));
                // add receiver
                for (int i = 0; i < receiver.tokens.size(); i++) {
                    Vector tv = (Vector) receiver.tokens.elementAt(i);
                    for (int j = 0; j < tv.size(); j++) {
                        TLAToken tok = (TLAToken) tv.elementAt(j);
                        recWithBrackets.addToken(tok);
                    }
                }
                recWithBrackets.addToken(PcalTranslate.BuiltInToken("]"));
                recWithBrackets.normalize();
            } else {
                recWithBrackets = new TLAExpr(new Vector());
            }

            sass.lhs.sub = recWithBrackets;

            TLAExpr expr = recWithBrackets.cloneAndNormalize();
            TLAExpr prefix = new TLAExpr();
            prefix.addLine();
            prefix.addToken(PcalTranslate.BuiltInToken(" Append("));
            prefix.addToken(PcalTranslate.IdentToken(queuesName));
            prefix.normalize();
            expr.prepend(prefix, 0);

            addMessageTokens(expr);

            expr.normalize();
            sass.rhs = expr;
            sass.setOrigin(this.getOrigin());

            AST.Assign assign = new AST.Assign();
            assign.ass = new Vector();
            assign.line = line;
            assign.col = col;
            assign.setOrigin(this.getOrigin());

            assign.ass.addElement(sass);

            // create "either or" to model an unreliable network
            AST.Either either = CreateEitherStmtOrSkip(assign);

            Vector result = new Vector();
            result.addElement(either);

            return result;
        }

    }

    public static class ReceiveCall extends AST {
        public String queuesName = PCalErlangConstants.GLOBAL_QUEUES_NAME; // read-only, global message queue name
        public String targetVarName = "";
        public TLAExpr targetExp = new TLAExpr(new Vector());

        public ReceiveCall() {
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[ChannelReceiver:" + NewLine() +
                            Indent(" channel |-> ") + getQueuesName() + "," +
                            EndIndent() + NewLine() +
                            Indent(" targetVar |-> ") + targetVarName + "," +
                            EndIndent() + NewLine() +
                            Indent(" targetExp |-> ") + targetExp + "]" +
                            EndIndent();
        }

        @Override
        public ReceiveCall deepCopy() {
            ReceiveCall result = new ReceiveCall();

            copyCommonASTFields(result);

            result.queuesName = this.queuesName;
            result.targetVarName = this.targetVarName;
            result.targetExp = this.targetExp.cloneAndNormalize();

            return result;
        }

        public String getQueuesName() {
            return queuesName;
        }

        public Vector GetReceiveStmts() {
            String queuesName = this.getQueuesName();
            Vector result = new Vector();

            TLAExpr exp = new TLAExpr();

            // when (Len(chanName[dim]) > 0) <headAssign> <tailAssign>
            AST.When when = new AST.When();
            when.col = line;
            when.line = col;
            // Len(chanName[dim]) > 0
            exp = new TLAExpr();
            exp.addLine();
            exp.addToken(PcalTranslate.BuiltInToken("Len("));
            exp.addToken(PcalTranslate.IdentToken(queuesName));
            exp.addToken(PcalTranslate.BuiltInToken("["));
            exp.addToken(PcalTranslate.IdentToken("self"));
            exp.addToken(PcalTranslate.BuiltInToken("]"));
            exp.addToken(PcalTranslate.BuiltInToken(") > 0 "));
            exp.normalize();
            when.exp = exp;
            when.setOrigin(this.getOrigin());
            // <headAssign> = targetVar := Head(chanName[dim])
            AST.Assign headAssign = new AST.Assign();
            headAssign.ass = new Vector();
            headAssign.line = line;
            headAssign.col = col;
            headAssign.setOrigin(this.getOrigin());
            // targetVar
            AST.SingleAssign sass = new AST.SingleAssign();
            sass.line = line;
            sass.col = col;
            sass.lhs.var = this.targetVarName;
            sass.lhs.sub = targetExp.cloneAndNormalize();
            // Head(chanName[dim])
            TLAExpr expr = new TLAExpr();
            expr.addLine();
            expr.addToken(PcalTranslate.BuiltInToken("Head("));
            expr.addToken(PcalTranslate.IdentToken(queuesName));
            expr.addToken(PcalTranslate.BuiltInToken("["));
            expr.addToken(PcalTranslate.IdentToken("self"));
            expr.addToken(PcalTranslate.BuiltInToken("]"));
            expr.addToken(PcalTranslate.BuiltInToken(")"));
            expr.normalize();
            sass.rhs = expr;
            sass.setOrigin(this.getOrigin());
            // set headAssign
            headAssign.ass.addElement(sass);
            // <tailAssign> = chanName[dim] := Tail(chanName[dim]/@)
            AST.Assign tailAssign = new AST.Assign();
            tailAssign.ass = new Vector();
            tailAssign.line = line;
            tailAssign.col = col;
            tailAssign.setOrigin(this.getOrigin());
            // chanName[dim]
            sass = new AST.SingleAssign();
            sass.line = line;
            sass.col = col;
            sass.lhs.var = queuesName;
            TLAExpr indexExpr = new TLAExpr();
            indexExpr.addLine();
            indexExpr.addToken(PcalTranslate.BuiltInToken("["));
            indexExpr.addToken(PcalTranslate.IdentToken("self"));
            indexExpr.addToken(PcalTranslate.BuiltInToken("]"));
            indexExpr.normalize();
            sass.lhs.sub = indexExpr;

            // Tail(chanName[dim]/@)
            expr = new TLAExpr();
            expr.addLine();
            String prevChannel = queuesName + "[self]";
            expr.addToken(PcalTranslate.BuiltInToken(" Tail(" + prevChannel + ") "));
            expr.normalize();
            sass.rhs = expr;
            sass.setOrigin(this.getOrigin());
            // set tailAssign
            tailAssign.ass.addElement(sass);
            // set result
            result.addElement(when);
            result.addElement(headAssign);
            result.addElement(tailAssign);

            return result;
        }

    }

    public static class GetAllProcsCall extends AST {

        public String targetVarName = "";
        public TLAExpr targetExp = new TLAExpr(new Vector());

        public GetAllProcsCall() {
        }

        public String toString() {
            return
                    Indent(lineCol()) +
                            "[GetAllProcsCall:" + NewLine() +
                            Indent(" targetVar |-> ") + targetVarName + "," +
                            EndIndent() + NewLine() +
                            Indent(" targetExp |-> ") + targetExp + "]" +
                            EndIndent();
        }

        @Override
        public GetAllProcsCall deepCopy() {
            GetAllProcsCall result = new GetAllProcsCall();

            copyCommonASTFields(result);

            result.targetExp = this.targetExp.cloneAndNormalize();
            result.targetVarName = this.targetVarName;

            return result;
        }

        public Vector getStmts() {
            Vector result = new Vector();

            AST.SingleAssign sass = new AST.SingleAssign();
            sass.line = line;
            sass.col = col;
            sass.lhs.var = this.targetVarName;
            sass.lhs.sub = this.targetExp.cloneAndNormalize();

            TLAExpr rightExpr = new TLAExpr();
            rightExpr.addLine();
            rightExpr.addToken(PcalTranslate.BuiltInToken("DOMAIN "));
            rightExpr.addToken(PcalTranslate.IdentToken(PCalErlangConstants.GLOBAL_QUEUES_NAME));
            rightExpr.normalize();

            sass.rhs = rightExpr;
            sass.setOrigin(this.getOrigin());

            AST.Assign assign = new AST.Assign();
            assign.ass = new Vector();
            assign.line = line;
            assign.col = col;
            assign.setOrigin(this.getOrigin());

            assign.ass.addElement(sass);

            result.addElement(assign);

            return result;
        }

    }

    public static class Fail extends AST {
        public When await;

        public Fail() {
            TLAExpr awaitExpr = new TLAExpr();
            awaitExpr.addLine();
            awaitExpr.addToken(PcalTranslate.BuiltInToken("FALSE"));
            awaitExpr.normalize();

            this.await = new AST.When();
            await.exp = awaitExpr;
            await.exp.setOrigin(this.getOrigin());
        }

        @Override
        public void setOrigin(Region origin) {
            super.setOrigin(origin);
            await.setOrigin(origin);
        }

        public String toString() {
            return lineCol() + "[type |-> \"fail\"]";
        }

        @Override
        public Fail deepCopy() {
            Fail result = new Fail();

            copyCommonASTFields(result);
            this.await = this.await.deepCopy();

            return result;
        }

        public Vector getStmts() {
            /**
             * Get the following statement:
             *  await FALSE;
             */
            Vector result = new Vector();

            result.addElement(this.await);
            return result;
        }

    }

    public static class MaybeFail extends AST {
        public Either either;

        public MaybeFail() {
            Fail failObj = new AST.Fail();
            either = CreateEitherStmtOrSkip(failObj);
        }

        public String toString() {
            return lineCol() + "[type |-> \"maybeFail\"]";
        }

        @Override
        public void setOrigin(Region origin) {
            super.setOrigin(origin);
            either.setOrigin(origin);
        }

        @Override
        public MaybeFail deepCopy() {
            MaybeFail result = new MaybeFail();

            copyCommonASTFields(result);
            this.either = this.either.deepCopy();

            return result;
        }

        public Vector getStmts() {
            /**
             * Get the following statement:
             *
             *  either
             *      fail();
             *  or
             *      skip;
             */

            Vector result = new Vector();

            result.addElement(either);
            return result;
        }

    }

}
