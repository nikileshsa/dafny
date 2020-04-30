using System;
using System.Text;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Linq;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Linq.Expressions;
using System.Runtime.CompilerServices;

namespace Microsoft.Dafny.Java {

  public abstract class AST {

    public static IVisitor<string,string> printer = new Printer();
    
    public String toString() { return this.accept(printer,null);}
    public abstract R accept<R, T>(IVisitor<R, T> v, T arg);

    public static void Test1() {
      var id = new Identifier("id");
      var s = new AssignStatement(id, id);
      MethodDeclaration md = new MethodDeclaration("mmm", new List<VarDeclaration>(), null,
        new BlockStatement(new Statement[] {s}));
      CompilationUnit cu = new CompilationUnit(null,null,null,new List<Declaration>());
      Console.Write(Printer.print(cu));
    }

    public abstract class IVisitor<R, T> {

      public R visit(AST ast, T arg) {
        throw new Exception("Unimplemented visitor method");
      }
      public abstract R visit(Program ast, T arg);
      public abstract R visit(CompilationUnit ast, T arg);
      public abstract R visit(SimpleType ast, T arg);
      public abstract R visit(ArrayType ast, T arg);
      public abstract R visit(CommentStatement ast, T arg);
      public abstract R visit(LabelledStatement ast, T arg);
      public abstract R visit(CommentExpr ast, T arg);
      public abstract R visit(ClassDeclaration ast, T arg);
      public abstract R visit(MethodDeclaration ast, T arg);
      public abstract R visit(BlockStatement ast, T arg);
      public abstract R visit(ExpressionStatement ast, T arg);
      public abstract R visit(AssignStatement ast, T arg);
      public abstract R visit(ReturnStatement ast, T arg);
      public abstract R visit(JumpStatement ast, T arg);
      public abstract R visit(IfStatement ast, T arg);
      public abstract R visit(WhileStatement ast, T arg);
      public abstract R visit(Identifier ast, T arg);
      public abstract R visit(Select ast, T arg);
      public abstract R visit(Index ast, T arg);
      public abstract R visit(NewArray ast, T arg);
      public abstract R visit(NewObject ast, T arg);
      public abstract R visit(Apply ast, T arg);
      public abstract R visit(Binary ast, T arg);
      public abstract R visit(Unary ast, T arg);
      public abstract R visit(Suffix ast, T arg);
      public abstract R visit(Paren ast, T arg);
      public abstract R visit(Literal ast, T arg);
      public abstract R visit(VarDeclaration ast, T arg);
      public abstract R visit(RequiresClause ast, T arg);
      public abstract R visit(EnsuresClause ast, T arg);
    }

    public class Program : AST {
      public IEnumerable<CompilationUnit> units;

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public class CompilationUnit : AST {
      public String openingComment;
      public Expression packageName; // May be null or a dot-separated sequence of names
      public List<Expression> imports;
      public List<Declaration> declarations;

      public CompilationUnit(String openingComment, Expression packageName,
        List<Expression> imports, List<Declaration> declarations) {
        this.declarations = declarations;
        this.imports = new List<Expression>();
        this.packageName = null;
        this.openingComment = null;
      }

      public CompilationUnit(CompilationUnit ast) : 
        this(ast.openingComment, ast.packageName, ast.imports, ast.declarations) {
      }

      public CompilationUnit() {
        this.declarations = new List<Declaration>();
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public abstract class Declaration : Statement {
    }

    public class ClassDeclaration : Declaration {
      public string name;
      public List<Declaration> members;

      public ClassDeclaration() :
        this(null, new List<Declaration>()) {
      }
      public ClassDeclaration(ClassDeclaration cd) :
        this(cd.name, cd.members) {
      }

      public ClassDeclaration(string name, List<Declaration> members) {
        this.name = name;
        this.members = members;
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }


    public abstract class Statement : AST {
      public Statement noindent() {
        if (this is BlockStatement) ((BlockStatement)this).noindent();
        return this;
      }

    }

    public abstract class Type : AST {
    }

    public class SimpleType : Type {
      public string type;

      public SimpleType(string type) {
        this.type = type;
      }
      public SimpleType(SimpleType e): this(e.type) {
      }
      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }   
    }

    public class ArrayType : Type {
      public Type type;
      public int dims;

      public ArrayType(Type type, int dims) {
        this.type = type;
        this.dims = dims;
      }
      public ArrayType(ArrayType e): this(e.type, e.dims) {
      }
      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }   
    }
    public abstract class Expression : AST {
      public Type type;
    }
    public class MethodDeclaration : Declaration {
      public string name;
      public string modifiers;
      public List<VarDeclaration> formals;
      public Type returnType;
      public BlockStatement body;
      public List<MethodSpecClause> clauses;

      public MethodDeclaration() {
        this.clauses = new List<MethodSpecClause>();
      }

      public MethodDeclaration(string name, List<VarDeclaration> formals, Type returnType, BlockStatement body) {
        this.name = name;
        this.formals = formals;
        this.returnType = returnType;
        this.body = body;
        this.clauses = new List<MethodSpecClause>();
        this.modifiers = "";
      }

      public MethodDeclaration(MethodDeclaration d) : this(d.name, d.formals, d.returnType, d.body) {
        this.clauses = new List<MethodSpecClause>(d.clauses);
        this.modifiers = d.modifiers;
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public class VarDeclaration : Declaration {
      public string modifiers;
      public string name;
      public Type type;
      public Expression init;

      public VarDeclaration(string name, Type type, Expression init) {
        this.modifiers = null;
        this.name = name;
        this.type = type;
        this.init = init;
      }

      public VarDeclaration(VarDeclaration d) : this(d.name, d.type, d.init) {
        this.modifiers = d.modifiers;
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public class BlockStatement : Statement {
      public List<Statement> statements;
      public bool noscope = false;
      public bool initialIndent = false;

      public BlockStatement(List<Statement> statements) {
        this.statements = statements;
      }
      public BlockStatement(params Statement[] statements) {
        this.statements = new List<Statement>(statements);
      }

      public BlockStatement() {
        this.statements = new List<Statement>();
      }

      public BlockStatement noindent() {
        this.initialIndent = false;
        return this;
      }

      public BlockStatement(BlockStatement ast) : this(ast.statements) {
        this.noscope = ast.noscope;
        this.initialIndent = ast.initialIndent;
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }


    public class CommentStatement : Statement {
      public string text;

      public CommentStatement(string text) {
        this.text = text;
      }

      public CommentStatement(CommentStatement ast) : this(ast.text) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public class LabelledStatement : Statement {
      public string label;
      public Statement statement;

      public LabelledStatement(string label, Statement statement) {
        this.label = label;
        this.statement = statement;
      }

      public LabelledStatement(LabelledStatement ast) : this(ast.label, ast.statement) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }
    
    public class ReturnStatement : Statement {
      public Expression result; // Possibly null

      public ReturnStatement(Expression result) {
        this.result = result;
      }

      public ReturnStatement(ReturnStatement ast) : this(ast.result) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }
    
    public class CommentExpr : Expression {
      public string text;

      public CommentExpr(string text) {
        this.text = text;
      }

      public CommentExpr(CommentExpr ast) : this(ast.text) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public class ExpressionStatement : Statement {
      public string kind;
      public Expression arg;

      public ExpressionStatement(Expression arg) {
        this.kind = null;
        this.arg = arg;
      }

      public ExpressionStatement(string kind, Expression arg) {
        this.kind = kind;
        this.arg = arg;
      }

      public ExpressionStatement(ExpressionStatement e): this(e.kind,e.arg) {
      }
      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }
    public class AssignStatement : Statement {
      public Expression lhs;
      public Expression rhs;

      public AssignStatement(Expression lhs, Expression rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
      }

      public AssignStatement(AssignStatement ast) : this(ast.lhs, ast.rhs) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public class WhileStatement : Statement {
      public Expression condition;
      public Statement body;

      public WhileStatement(Expression condition, Statement body) {
        this.condition = condition;
        this.body = body;
      }

      public WhileStatement(WhileStatement ast) : this(ast.condition, ast.body) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public class IfStatement : Statement {
      public Expression condition;
      public Statement thenStatement;
      public Statement elseStatement; // possibly null

      public IfStatement(Expression condition, Statement thenStatement, Statement elseStatement) {
        this.condition = condition;
        this.thenStatement = thenStatement;
        this.elseStatement = elseStatement;
      }

      public IfStatement(IfStatement ast) : this(ast.condition, ast.thenStatement, ast.elseStatement) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public class JumpStatement : Statement {
      public string kind;
      public string target; // possibly null

      public JumpStatement(string kind, string target) {
        this.kind = kind;
        this.target = target;
      }

      public JumpStatement(JumpStatement ast) : this(ast.kind, ast.target) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public class Paren : Expression {
      public Expression arg;

      public Paren(Expression arg) {
        this.arg = arg;
      }

      public Paren(Paren e) : this(e.arg) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }
    public class Identifier : Expression {
      public Declaration declaration; // declaration associated with the id
      public string id;

      public Identifier(string id) {
        this.id = id;
      }

      public Identifier(Identifier id) : this(id.id) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }
    public class Select : Expression {
      public Expression selector;
      public string id;

      public Select(Expression selector, string id) {
        this.id = id;
        this.selector = selector;
      }

      public Select(Select e) : this(e.selector, e.id) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public class Index : Expression {
      public Expression array;
      public Expression index;

      public Index(Expression array, Expression index) {
        this.array = array;
        this.index = index;
      }

      public Index(Index e) : this(e.array, e.index) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public class Binary : Expression {
      public Expression lhs;
      public string op;
      public Expression rhs;

      public Binary(Expression lhs, string op, Expression rhs) : this(lhs, op, rhs, null) {
      }

      public Binary(Expression lhs, string op, Expression rhs, Type t) {
        this.lhs = lhs;
        this.op = op;
        this.rhs = rhs;
        this.type = t;
      }

      public Binary(Binary e) : this(e.lhs, e.op, e.rhs, e.type) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public class Unary : Expression {
      public string op;
      public Expression arg;

      public Unary(string op, Expression arg): this(op, arg, null) {
      }
      public Unary(string op, Expression arg, Type t) {
        this.op = op;
        this.arg = arg;
        this.type = t;
      }

      public Unary(Unary e) : this(e.op, e.arg, e.type) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public class Suffix : Expression {
      public string suffix;
      public Expression arg;

      public Suffix(Expression arg, string suffix) {
        this.arg = arg;
        this.suffix = suffix;
      }

      public Suffix(Suffix e) : this(e.arg, e.suffix) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }


    
    public class Literal : Expression {
      public string text;

      public Literal(string text) {
        this.text = text;
      }

      public Literal(Literal e) : this(e.text) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }
    public class NewArray : Expression {
      public Type type;
      public Expression dim; // TODO - multiple dimensions

      public NewArray(Type type, Expression dim) {
        this.type = type;
        this.dim = dim;
      }

      public NewArray(NewArray e) : this(e.type, e.dim) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }
    public class NewObject : Expression {
      public Type type;

      public NewObject(Type type) {
        this.type = type;
      }

      public NewObject(NewObject e) : this(e.type) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }
    public class Apply : Expression {
      public Expression method;
      public List<Expression> args;

      public Apply(Expression method, List<Expression> args) {
        this.method = method;
        this.args = args;
      }

      public Apply(Expression method, params Expression[] args) {
        this.method = method;
        this.args = new List<Expression>(args);
      }

      public Apply(Apply e) : this(e.method, e.args) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }

    public abstract class MethodSpecClause : AST {
    }
    public class RequiresClause : MethodSpecClause {
      public Expression expr;
   
      public RequiresClause(Expression expr) {
        this.expr = expr;
      }

      public RequiresClause(RequiresClause e) : this(e.expr) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }
    public class EnsuresClause : MethodSpecClause {
      public Expression expr;
   
      public EnsuresClause(Expression expr) {
        this.expr = expr;
      }

      public EnsuresClause(EnsuresClause e) : this(e.expr) {
      }

      public override R accept<R, T>(IVisitor<R, T> v, T arg) {
        return v.visit(this, arg);
      }
    }
    public class Printer : IVisitor<string, string> {

      static public string eol = "\n";
      public string indentamt = "  ";

      public string inline(AST ast) {
        return ast == null ? "*NULL*" : ast.accept(this, "");
      }

      public string print(AST ast, string indent) {
        return ast == null ? "*NULL*" : ast.accept(this, indent);
      }

      public static string print(AST ast) {
        var p = new Printer();
        return ast.accept(p, "");
      }


      public override string visit(Program ast, string indent) {
        string ret = "";
        foreach (CompilationUnit cu in ast.units) {
          ret = ret + print(cu, indent);
        }

        return ret;
      }

      public override string visit(CompilationUnit ast, string indent) {
        string ret = ast.openingComment == null ? "" : (ast.openingComment+eol);

        if (ast.packageName != null) ret += "package " + print(ast.packageName, indent) + ";";
        
        if (ast.imports != null) {
          foreach (Expression imp in ast.imports) {
            ret += "import " + print(imp, indent) + ";";
          }
        }

        if (ast.declarations != null) {
          foreach (Declaration cu in ast.declarations) {
            ret += print(cu, indent);
          }
        }

        return ret;
      }

      public override string visit(SimpleType ast, string indent) {
        return ast.type;
      }
      public override string visit(ArrayType ast, string indent) {
        return inline(ast.type)+"[]";
      }
      public override string visit(Identifier ast, string indent) {
        return ast.id;
      }
      public override string visit(Select ast, string indent) {
        return inline(ast.selector) + "." + ast.id;
      }

      public override string visit(Index ast, string indent) {
        return inline(ast.array) + "[" + inline(ast.index) + "]";
      }

      public override string visit(Literal ast, string indent) {
        return ast.text;
      }

      public override string visit(NewObject ast, string indent) {
        return "new " + inline(ast.type) + "()"; // TODO - needs arguments
      }

      public override string visit(NewArray ast, string indent) {
        return "new " + inline(ast.type) + "[" + inline(ast.dim) + "]";
      }

      public override string visit(Apply ast, string indent) {
        return inline(ast.method) + "(" + inline(ast.args) + ")";
      }

      public string inline(List<Expression> args) {
        string ret = "";
        if (args.Count == 0) return ret;
        bool isFirst = true;
        foreach (Expression e in args) {
          if (isFirst) isFirst = true;
          else ret += ", ";
          ret += inline(e);
        }
        return ret;
      }

      public override string visit(Binary ast, string indent) {
        return inline(ast.lhs) + " " + ast.op + " " + inline(ast.rhs);
      }

      public override string visit(Unary ast, string indent) {
        return ast.op + inline(ast.arg);
      }

      public override string visit(Suffix ast, string indent) {
        return inline(ast.arg) + "." + ast.suffix;
      }

      public override string visit(CommentStatement ast, string indent) {
        return indent + "// " + ast.text + eol;
      }
      public override string visit(CommentExpr ast, string indent) {
        return "/* " + ast.text + " */";
      }
      public override string visit(Paren ast, string indent) {
        return "(" + inline(ast.arg) + ")";
      }

      public override string visit(BlockStatement ast, string indent) {
        if (ast.noscope) {
          string ret = "";
          foreach (Statement s in ast.statements) ret = ret + print(s, indent);
          return ret;
        } else {
          string ret = (ast.initialIndent?indent:"") + "{" + eol;
          foreach (Statement s in ast.statements) ret += print(s, indent + indentamt);
          return ret + indent + "}" + eol;
        }
      }

      public override string visit(LabelledStatement ast, string ident) {
        return ident + ast.label + ": " + print(ast.statement, ident); // TODO - indenting likely wrong
      }

      public override string visit(ExpressionStatement ast, string indent) {
        if (ast.kind == null) {
          return indent + inline(ast.arg) + ";" + eol;
        } else {
          return indent + "//@ " + ast.kind + " " + inline(ast.arg) + ";" + eol;
        }
      }

      public override string visit(AssignStatement ast, string indent) {
        return indent + print(ast.lhs, indent) + " = " + print(ast.rhs, indent) + ";" + eol;
      }

      public override string visit(ReturnStatement ast, string indent) {
        return indent + "return " + (ast.result != null ? print(ast.result, indent) : "") + ";" + eol;
      }

      public override string visit(JumpStatement ast, string indent) {
        return indent + ast.kind + (ast.target != null ? (" " + ast.target) : "") + ";" + eol;
      }

      public override string visit(WhileStatement ast, string indent) {
        return indent + "while (" + inline(ast.condition) + ") " + print(ast.body, indent) + eol;
      }

      public override string visit(IfStatement ast, string indent) {
        string ret = indent + "if (" + inline(ast.condition) + ") " + print(ast.thenStatement, indent);
        if (ast.elseStatement != null) {
          string z = "}" + eol;
          if (ret.EndsWith(z)) ret = ret.Substring(0, ret.Length - eol.Length);
          ret += " else " + print(ast.elseStatement, indent);
        }
        return ret + eol;
      }

      public override string visit(ClassDeclaration ast, string indent) {
        string ret = indent + "public class " + ast.name + "{" + eol;
        foreach (Declaration d in ast.members) {
          ret += d.accept(this, indent + indentamt);
        }
        ret += indent + "}" + eol;
        return ret;
      }

      public override string visit(MethodDeclaration ast, string indent) {
        string ret = "";
        foreach (MethodSpecClause cl in ast.clauses) {
          ret += print(cl, indent);
        }
        ret += indent + ast.modifiers + " " + inline(ast.returnType) + " " + ast.name + "(";
        bool first = true;
        foreach (VarDeclaration d in ast.formals) {
          if (first) first = false; else ret += ",";
          ret += d.type.accept(this, indent) + " " + d.name;
        }
        ret += ") ";
        ret += print(ast.body, indent) + eol;
        return ret;
      }

      public override string visit(VarDeclaration ast, string indent) {
        string ret = indent + (ast.modifiers==null? "" : (ast.modifiers+" ")) + print(ast.type, indent) + " " + ast.name
          + (ast.init == null ? "" : (" = " + print(ast.init,indent))) + ";" + eol;
        return ret;
      }

      public override string visit(RequiresClause ast, string ident) {
        return ident + "//@ " + "requires " + inline(ast.expr) + ";" + eol;
      }

      public override string visit(EnsuresClause ast, string ident) {
        return ident + "//@ " + "ensures " + inline(ast.expr) + ";" + eol;
      }

    }
  }
}
