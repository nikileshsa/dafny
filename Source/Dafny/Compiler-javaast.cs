//-----------------------------------------------------------------------------
//
// Copyright (C) Amazon.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.IO;
using System.Diagnostics.Contracts;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Text.RegularExpressions;
using System.Reflection;
using Microsoft.Dafny.Java;
using Bpl = Microsoft.Boogie;



namespace Microsoft.Dafny {
  public class JavaASTCompiler : Compiler {
    public JavaASTCompiler(ErrorReporter reporter)
      : base(reporter) {
      IntSelect = ",java.math.BigInteger";
      LambdaExecute = ".apply";
    }

    public override String TargetLanguage => "Java";


    // Shadowing variables in Compiler.cs
    new string DafnySetClass = "dafny.DafnySet";
    new string DafnyMultiSetClass = "dafny.DafnyMultiset";
    new string DafnySeqClass = "dafny.DafnySequence";
    new string DafnyMapClass = "dafny.DafnyMap";

    const string DafnyBigRationalClass = "dafny.BigRational";
    const string DafnyEuclideanClass = "dafny.DafnyEuclidean";
    const string DafnyHelpersClass = "dafny.Helpers";
    const string TypeClass = "dafny.Type";

    const string DafnyFunctionIfacePrefix = "dafny.Function";
    const string DafnyMultiArrayClassPrefix = "dafny.Array";
    const string DafnyTupleClassPrefix = "dafny.Tuple";

    private TextWriter errorWr;
    public Dictionary<string, string> results = null;
    string DafnyMultiArrayClass(int dim) => DafnyMultiArrayClassPrefix + dim;
    string DafnyTupleClass(int size) => DafnyTupleClassPrefix + size;

    string DafnyFunctionIface(int arity) =>
      arity == 1 ? "java.util.function.Function" : DafnyFunctionIfacePrefix + arity;

    static string FormatExternBaseClassName(string externClassName) =>
      $"_ExternBase_{externClassName}";

    static string FormatTypeDescriptorVariable(string typeVarName) =>
      $"_td_{typeVarName}";

    static string FormatTypeDescriptorVariable(TypeParameter tp) =>
      FormatTypeDescriptorVariable(tp.CompileName);

    const string TypeMethodName = "_type";

    private String ModuleName;
    private String ModulePath;
    private int FileCount = 0;
    private Import ModuleImport;
    private HashSet<int> tuples = new HashSet<int>();
    private HashSet<int> functions = new HashSet<int>();
    private HashSet<int> arrays = new HashSet<int>();

    private AST.CompilationUnit currentCompilationUnit;

    private readonly List<Import> Imports = new List<Import>();

    //RootImportWriter writes additional imports to the main file.
    //private TargetWriter RootImportWriter;

    private struct Import {
      public string Name, Path;
    }

    protected override bool UseReturnStyleOuts(Method m, int nonGhostOutCount) => true;

    public override bool SupportsInMemoryCompilation => false;

    protected override bool SupportsAmbiguousTypeDecl => false;
    protected override bool SupportsProperties => false;
    protected override bool NeedsWrappersForInheritedFields => false;
    protected override bool FieldsInTraits => false;

    private enum JavaNativeType {
      Byte,
      Short,
      Int,
      Long
    }

    public override void Compile(Program program, TargetWriter wrx) {
      Contract.Requires(program != null);

      string filename = program.FullName;
      if (filename.EndsWith(".dfy")) filename = filename.Substring(0, filename.Length - 3) + "java";
      else filename = filename + ".java";
      
      string root = program.FullName;
      root = root.Substring(0,root.Length - 4); // remove .dfy
      int k = root.LastIndexOf('.');
      if (k >= 0) root = root.Substring(k+1);
      k = root.LastIndexOf('\\');
      if (k >= 0) root = root.Substring(k + 1);

      Java.AST.CompilationUnit cu = new Java.AST.CompilationUnit();
      currentCompilationUnit = cu;
      //cu.name = program.name;
      EmitHeader(program, null);

      //EmitBuiltInDecls(program.BuiltIns, wrx); // TODO
      var temp = new List<ModuleDefinition>();
      OrganizeModules(program, out temp);
      program.CompileModules = temp;

      foreach (ModuleDefinition m in program.CompileModules) {
        if (m.FullName.Equals("_System")) continue; // TODO
        if (m.IsAbstract) {
          // the purpose of an abstract module is to skip compilation
          continue;
        }

        if (!m.IsToBeCompiled) {
          continue;
        }

        var moduleIsExtern = false;
        string libraryName = null;
        if (!DafnyOptions.O.DisallowExterns) {
          var args = Attributes.FindExpressions(m.Attributes, "extern");
          if (args != null) {
            if (args.Count == 2) {
              libraryName = (string) (args[1] as StringLiteralExpr)?.Value;
            }

            moduleIsExtern = true;
          }
        }

        var wr = CreateModule(m.CompileName, m.IsDefaultModule, moduleIsExtern, libraryName, wrx);
        foreach (TopLevelDecl d in m.TopLevelDecls) {
           bool compileIt = true;
          if (Attributes.ContainsBool(d.Attributes, "compile", ref compileIt) && !compileIt) {
            continue;
          }

          if (d is OpaqueTypeDecl) {
            var at = (OpaqueTypeDecl) d;
            Error(d.tok, "Opaque type ('{0}') cannot be compiled", wr, at.FullName);
          }
          else if (d is TypeSynonymDecl) {
            var sst = d as SubsetTypeDecl;
            if (sst != null) {
              // TODO: DeclareSubsetType(sst, wr);
            }
          }
          else if (d is NewtypeDecl) {
            var nt = (NewtypeDecl) d;
            // TODO: var w = DeclareNewtype(nt, wr);
            // TODO: CompileClassMembers(nt, w);
          }
          else if (d is DatatypeDecl) {
            var dt = (DatatypeDecl) d;
            // TODO: CheckForCapitalizationConflicts(dt.Ctors);
            foreach (var ctor in dt.Ctors) {
              // TODO: CheckForCapitalizationConflicts(ctor.Destructors);
            }

            var w = DeclareDatatype(dt, wr);
            if (w != null) {
              // TODO: CompileClassMembers(dt, w);
            }
          }
          else if (d is IteratorDecl) {
            // TODO
            // var iter = (IteratorDecl)d;
            // if (DafnyOptions.O.ForbidNondeterminism && iter.Outs.Count > 0) {
            //   Error(iter.tok, "since yield parameters are initialized arbitrarily, iterators are forbidden by /definiteAssignment:3 option", wr);
            // }
            //
            // var wIter = CreateIterator(iter, wr);
            // if (iter.Body == null) {
            //   Error(iter.tok, "Iterator {0} has no body", wIter, iter.FullName);
            // } else {
            //   TrStmtList(iter.Body.Body, wIter);
            // }

          }
          else if (d is TraitDecl) {
            // writing the trait
            // TODO: 
            // var trait = (TraitDecl)d;
            // var w = CreateTrait(trait.CompileName, trait.IsExtern(out _, out _), null, null, wr);
            // CompileClassMembers(trait, w);
          }
          else if (d is ClassDecl) {
            var cl = (ClassDecl) d;
            var include = true;
            if (cl.IsDefaultClass) {
              Predicate<MemberDecl> compilationMaterial = x =>
                !x.IsGhost && (DafnyOptions.O.DisallowExterns || !Attributes.Contains(x.Attributes, "extern"));
              include = cl.Members.Exists(compilationMaterial) || cl.InheritedMembers.Exists(compilationMaterial);
            }

            var classIsExtern = false;
            if (include) {
              classIsExtern = !DafnyOptions.O.DisallowExterns && Attributes.Contains(cl.Attributes, "extern") ||
                              cl.IsDefaultClass && Attributes.Contains(cl.Module.Attributes, "extern");
              if (classIsExtern && cl.Members.TrueForAll(member =>
                    member.IsGhost || Attributes.Contains(member.Attributes, "extern"))) {
                include = false;
              }
            }

            errorWr = wr;

            AST.ClassDeclaration ast = TrClass(cl, root);
            cu.declarations.Add(ast);
            // if (include) {
            //   var cw = CreateClass(IdName(cl), classIsExtern, cl.FullName, cl.TypeArgs, cl.TraitsTyp, cl.tok, wr);
            //   // TODO: CompileClassMembers(cl, cw);
            //   cw.Finish();
            // } else {
            //   // still check that given members satisfy compilation rules
            //   var abyss = new NullClassWriter();
            //   // TODO: CompileClassMembers(cl, abyss);
            // }
          }
          else if (d is ValuetypeDecl) {
            // nop
          }
          else if (d is ModuleDecl) {
            // nop
          }
          else {
            Contract.Assert(false);
          }
        }

//        FinishModule();
      }

      string javaProgram = AST.Printer.print(cu);
      System.IO.File.WriteAllText(filename, javaProgram);
      Console.WriteLine(javaProgram);
      Console.WriteLine("END");
    }


    private static JavaNativeType AsJavaNativeType(NativeType.Selection sel) {
      switch (sel) {
        case NativeType.Selection.Byte:
        case NativeType.Selection.SByte:
          return JavaNativeType.Byte;
        case NativeType.Selection.Short:
        case NativeType.Selection.UShort:
          return JavaNativeType.Short;
        case NativeType.Selection.Int:
        case NativeType.Selection.UInt:
          return JavaNativeType.Int;
        case NativeType.Selection.Long:
        case NativeType.Selection.ULong:
          return JavaNativeType.Long;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();
      }
    }

    private static JavaNativeType AsJavaNativeType(NativeType nt) {
      return AsJavaNativeType(nt.Sel);
    }

    private JavaNativeType? AsJavaNativeType(Type type) {
      var nt = AsNativeType(type);
      if (nt == null) {
        return null;
      }
      else {
        return AsJavaNativeType(nt);
      }
    }

    protected override void DeclareSpecificOutCollector(string collectorVarName, TargetWriter wr, List<Type> types,
      List<Type> formalTypes, List<Type> lhsTypes) {
      // If the method returns an array of parameter type, and we're assigning
      // to a variable with a more specific type, we need to insert a cast:
      //
      // Array<Integer> outcollector42 = obj.Method(); // <-- you are here
      // int[] out43 = (int[]) outcollector42.unwrap();
      var returnedTypes = new List<string>();
      Contract.Assert(formalTypes.Count == lhsTypes.Count);
      for (var i = 0; i < formalTypes.Count; i++) {
        var formalType = formalTypes[i];
        var lhsType = lhsTypes[i];
        if (formalType.IsArrayType && formalType.AsArrayType.Dims == 1 &&
            UserDefinedType.ArrayElementType(formalType).IsTypeParameter) {
          returnedTypes.Add("java.lang.Object");
        }
        else {
          returnedTypes.Add(TypeName(lhsType, wr, Bpl.Token.NoToken, boxed: types.Count > 1));
        }
      }

      if (types.Count > 1) {
        tuples.Add(types.Count);
        wr.Write($"{DafnyTupleClassPrefix}{types.Count}<{Util.Comma(returnedTypes)}> {collectorVarName} = ");
      }
      else {
        wr.Write($"{returnedTypes[0]} {collectorVarName} = ");
      }
    }

    protected override void EmitCastOutParameterSplits(string outCollector, List<string> lhsNames,
      TargetWriter wr, List<Type> outTypes, List<Type> formalTypes, List<Type> lhsTypes, Bpl.IToken tok) {
      var wOuts = new List<TargetWriter>();
      for (var i = 0; i < lhsNames.Count; i++) {
        wr.Write($"{lhsNames[i]} = ");
        //
        // Suppose we have:
        //
        //   method Foo<A>(a : A) returns (arr : array<A>)
        //
        // This is compiled to:
        //
        //   public <A> Object Foo(A a)
        //
        // (There's also an argument for the type descriptor, but I'm omitting
        // it for clarity.)  Foo returns Object, not A[], since A could be
        // primitive and primitives cannot be generic parameters in Java
        // (*sigh*).  So when we call it:
        //
        //   var arr : int[] := Foo(42);
        //
        // we have to add a type cast:
        //
        //   BigInteger[] arr = (BigInteger[]) Foo(new BigInteger(42));
        //
        // Things can get more complicated than this, however.  If the method returns
        // the array as part of a tuple:
        //
        //   method Foo<A>(a : A) returns (pair : (array<A>, array<A>))
        //
        // then we get:
        //
        //   public <A> Tuple2<Object, Object> Foo(A a)
        //
        // and we have to write:
        //
        //   BigInteger[] arr = (Pair<BigInteger[], BigInteger[]>) (Object) Foo(new BigInteger(42));
        //
        // (Note the extra cast to Object, since Java doesn't allow a cast to
        // change a type parameter, as that's unsound in general.  It just
        // happens to be okay here!)
        //
        // Rather than try and exhaustively check for all the circumstances
        // where a cast is necessary, for the moment we just always cast to the
        // LHS type via Object, which is redundant 99% of the time but not
        // harmful.
        wr.Write($"({TypeName(lhsTypes[i], wr, Bpl.Token.NoToken)}) (Object) ");
        if (lhsNames.Count == 1) {
          wr.Write(outCollector);
        }
        else {
          wr.Write($"{outCollector}.dtor__{i}()");
        }

        EndStmt(wr);
      }
    }

    protected override void EmitMemberSelect(AssignStmt s0, List<Type> tupleTypeArgsList, TargetWriter wr, string tup) {
      wr.Write("(");
      var lhs = (MemberSelectExpr) s0.Lhs;
      var wCoerced = EmitCoercionIfNecessary(from: null, to: tupleTypeArgsList[0], tok: s0.Tok, wr: wr);
      wCoerced.Write($"({TypeName(tupleTypeArgsList[0].NormalizeExpand(), wCoerced, s0.Tok)})");
      EmitTupleSelect(tup, 0, wCoerced);
      wr.Write(")");
      wr.Write($".{IdMemberName(lhs)} = ");
      wCoerced = EmitCoercionIfNecessary(from: null, to: tupleTypeArgsList[1], tok: s0.Tok, wr: wr);
      wCoerced.Write($"({TypeName(tupleTypeArgsList[1].NormalizeExpand(), wCoerced, s0.Tok)})");
      EmitTupleSelect(tup, 1, wCoerced);
      EndStmt(wr);
    }

    protected override void EmitSeqSelect(AssignStmt s0, List<Type> tupleTypeArgsList, TargetWriter wr, string tup) {
      wr.Write("(");
      var lhs = (SeqSelectExpr) s0.Lhs;
      TargetWriter wColl, wIndex, wValue;
      EmitIndexCollectionUpdate(out wColl, out wIndex, out wValue, wr, nativeIndex: true);
      var wCoerce = EmitCoercionIfNecessary(from: null, to: lhs.Seq.Type, tok: s0.Tok, wr: wColl);
      wCoerce.Write($"({TypeName(lhs.Seq.Type.NormalizeExpand(), wCoerce, s0.Tok)})");
      EmitTupleSelect(tup, 0, wCoerce);
      wColl.Write(")");
      var wCast = EmitCoercionToNativeInt(wIndex);
      EmitTupleSelect(tup, 1, wCast);
      wValue.Write($"({TypeName(tupleTypeArgsList[2].NormalizeExpand(), wValue, s0.Tok)})");
      EmitTupleSelect(tup, 2, wValue);
      EndStmt(wr);
    }

    protected override void EmitMultiSelect(AssignStmt s0, List<Type> tupleTypeArgsList, TargetWriter wr, string tup,
      int L) {
      wr.Write("(");
      var lhs = (MultiSelectExpr) s0.Lhs;
      var wArray = new TargetWriter(wr.IndentLevel, true);
      var wCoerced = EmitCoercionIfNecessary(from: null, to: tupleTypeArgsList[0], tok: s0.Tok, wr: wArray);
      wCoerced.Write($"({TypeName(tupleTypeArgsList[0].NormalizeExpand(), wCoerced, s0.Tok)})");
      EmitTupleSelect(tup, 0, wCoerced);
      wArray.Write(")");
      var array = wArray.ToString();
      var indices = new List<string>();
      for (int i = 0; i < lhs.Indices.Count; i++) {
        var wIndex = new TargetWriter();
        wIndex.Write("((java.math.BigInteger)");
        EmitTupleSelect(tup, i + 1, wIndex);
        wIndex.Write(")");
        indices.Add(wIndex.ToString());
      }

      var lv = EmitArraySelectAsLvalue(array, indices, tupleTypeArgsList[L - 1]);
      var wrRhs = EmitAssignment(lv, tupleTypeArgsList[L - 1], null, wr);
      wrRhs.Write($"(({TypeName(tupleTypeArgsList[L - 1], wrRhs, s0.Tok)})");
      EmitTupleSelect(tup, L - 1, wrRhs);
      wrRhs.Write(")");
      EndStmt(wr);
    }

    protected override void WriteCast(string s, TargetWriter wr) {
      wr.Write($"({s})");
    }

    protected override TargetWriter DeclareLocalVar(string name, Type /*?*/ type, Bpl.IToken /*?*/ tok, TargetWriter wr,
      Type t) {
      return DeclareLocalVar(name, t, tok, wr);
    }

    protected override void DeclareLocalVar(string name, Type /*?*/ type, Bpl.IToken /*?*/ tok, Expression rhs,
      bool inLetExprBody, TargetWriter wr, Type t) {
      var w = DeclareLocalVar(name, t, tok, wr);
      TrExpr(rhs, w, inLetExprBody);
    }

    protected override TargetWriter EmitIngredients(TargetWriter wr, string ingredients, int L, string tupleTypeArgs,
      ForallStmt s, AssignStmt s0, Expression rhs) {
      using (var wrVarInit = wr) {
        wrVarInit.Write($"java.util.ArrayList<{DafnyTupleClassPrefix}{L}<{tupleTypeArgs}>> {ingredients} = ");
        AddTupleToSet(L);
        EmitEmptyTupleList(tupleTypeArgs, wrVarInit);
      }

      var wrOuter = wr;
      wr = CompileGuardedLoops(s.BoundVars, s.Bounds, s.Range, wr);
      using (var wrTuple = EmitAddTupleToList(ingredients, tupleTypeArgs, wr)) {
        wrTuple.Write($"{L}<{tupleTypeArgs}>(");
        if (s0.Lhs is MemberSelectExpr lhs1) {
          TrExpr(lhs1.Obj, wrTuple, false);
        }
        else if (s0.Lhs is SeqSelectExpr lhs2) {
          TrExpr(lhs2.Seq, wrTuple, false);
          wrTuple.Write(", ");
          TrParenExpr(lhs2.E0, wrTuple, false);
        }
        else {
          var lhs = (MultiSelectExpr) s0.Lhs;
          TrExpr(lhs.Array, wrTuple, false);
          foreach (var t in lhs.Indices) {
            wrTuple.Write(", ");
            TrParenExpr(t, wrTuple, false);
          }
        }

        wrTuple.Write(", ");
        if (rhs is MultiSelectExpr) {
          Type t = rhs.Type.NormalizeExpand();
          wrTuple.Write($"({TypeName(t, wrTuple, rhs.tok)})");
        }

        TrExpr(rhs, wrTuple, false);
      }

      return wrOuter;
    }

    protected override void EmitHeader(Program program, TargetWriter wr) {
      currentCompilationUnit.openingComment =
        $"// Dafny program {program.Name} compiled into Java with the JavaAST compiler";
      ModuleName = HasMain(program, out _) ? "main" : Path.GetFileNameWithoutExtension(program.Name);
    }

    // Only exists to make sure method is overriden
    protected override void EmitBuiltInDecls(BuiltIns builtIns, TargetWriter wr) {
    }

    public override void EmitCallToMain(Method mainMethod, TargetWriter wr) {
      var companion = TypeName_Companion(mainMethod.EnclosingClass as ClassDecl, wr, mainMethod.tok);
      var wBody = wr.NewNamedBlock("public static void main(String[] args)");
      var modName = mainMethod.EnclosingClass.Module.CompileName == "_module" ? "_System." : "";
      companion = modName + companion;
      Coverage.EmitSetup(wBody);
      wBody.WriteLine($"{DafnyHelpersClass}.withHaltHandling({companion}::{IdName(mainMethod)});");
      Coverage.EmitTearDown(wBody);
    }

    void EmitImports(TargetWriter wr, out TargetWriter importWriter) {
      importWriter = wr.ForkSection();
      foreach (var import in Imports) {
        if (import.Name != ModuleName) {
          EmitImport(import, importWriter);
        }
      }
    }

    private void EmitImport(Import import, TargetWriter importWriter) {
      importWriter.WriteLine($"import {import.Path.Replace('/', '.')}.*;");
    }

    protected override TargetWriter CreateModule(string moduleName, bool isDefault, bool isExtern,
      string /*?*/ libraryName, TargetWriter wr) {
      if (isDefault) {
        // Fold the default module into the main module
        return wr;
      }

      var pkgName = libraryName ?? IdProtect(moduleName);
      var path = pkgName.Replace('.', '/');
      var import = new Import {Name = moduleName, Path = path};
      ModuleName = IdProtect(moduleName);
      ModulePath = path;
      ModuleImport = import;
      FileCount = 0;
      return wr;
    }

    protected override void FinishModule() {
      if (FileCount > 0) {
        AddImport(ModuleImport);
      }

      FileCount = 0;
    }

    private void AddImport(Import import) {
      if (!Imports.Contains(import)) {
        //EmitImport(import, RootImportWriter);
        Imports.Add(import);
      }
    }

    protected override void DeclareSubsetType(SubsetTypeDecl sst, TargetWriter wr) {
      // TODO
      // ClassWriter cw = CreateClass(IdName(sst), sst.TypeArgs, wr) as ClassWriter;
      // if (sst.WitnessKind == SubsetTypeDecl.WKind.Compiled){
      //   var sw = new TargetWriter(cw.InstanceMemberWriter.IndentLevel, true);
      //   TrExpr(sst.Witness, sw, false);
      //   cw.DeclareField("Witness", true, true, sst.Rhs, sst.tok, sw.ToString());
      // }
    }

    protected AST.ClassDeclaration TrClass(ClassDecl cl, string root) {
      string name = IdName(cl);
      if (cl.IsDefaultClass) {
        name = root;
      }
      var include = true;
      if (cl.IsDefaultClass) {
        Predicate<MemberDecl> compilationMaterial = x =>
          !x.IsGhost && (DafnyOptions.O.DisallowExterns || !Attributes.Contains(x.Attributes, "extern"));
        include = cl.Members.Exists(compilationMaterial) || cl.InheritedMembers.Exists(compilationMaterial);
      }

      var classIsExtern = false;
      if (include) {
        classIsExtern = !DafnyOptions.O.DisallowExterns && Attributes.Contains(cl.Attributes, "extern") ||
                        cl.IsDefaultClass && Attributes.Contains(cl.Module.Attributes, "extern");
        if (classIsExtern &&
            cl.Members.TrueForAll(member => member.IsGhost || Attributes.Contains(member.Attributes, "extern"))) {
          include = false;
        }
      }

      string fullPrintName = cl.FullName;
      List<TypeParameter> typeParameters = cl.TypeArgs;
      List<Type> superclasses = cl.TraitsTyp;
      Bpl.IToken tok = cl.tok;
      var javaName = classIsExtern ? FormatExternBaseClassName(name) : name;
      var filename = $"{ModulePath}/{javaName}.java";
      FileCount += 1;
      AST.ClassDeclaration cd = new AST.ClassDeclaration();
      cd.name = javaName;
      // TODO: modifiers?
      // TODO: type parameters?
      // TODO: superclass, interfaces?

      CompileClassMembers(cd, cl, errorWr);
      return cd;

    }

    void CompileClassMembers(AST.ClassDeclaration cd, TopLevelDeclWithMembers c, TextWriter errorWr) {
      Contract.Requires(cd != null);
      Contract.Requires(c != null);
      Contract.Requires(errorWr != null);
      Contract.Requires(thisContext == null);
      Contract.Ensures(thisContext == null);

      thisContext = c;

      if (c is ClassDecl) {
        CheckHandleWellformed((ClassDecl) c, errorWr);
      }

      var inheritedMembers = c is ClassDecl ? ((ClassDecl) c).InheritedMembers : new List<MemberDecl>();

      CheckForCapitalizationConflicts(c.Members, inheritedMembers);
      OrderedBySCC(inheritedMembers, c);
      OrderedBySCC(c.Members, c);

      foreach (var member in inheritedMembers) {
        Contract.Assert(!member.IsStatic); // only instance members should ever be added to .InheritedMembers
        if (member.IsGhost) {
          // skip
        }
        else if (member is ConstantField && SupportsProperties) {
          if (NeedsWrappersForInheritedFields) {
            var cf = (ConstantField) member;
            if (cf.Rhs == null) {
              Contract.Assert(!cf.IsStatic); // as checked above, only instance members can be inherited
              // TODO: classWriter.DeclareField("_" + cf.CompileName, false, false, cf.Type, cf.tok, DefaultValue(cf.Type, errorWr, cf.tok, true));
            }

//            var w = classWriter.CreateGetter(IdName(cf), cf.Type, cf.tok, false, true, member);
//            Contract.Assert(w != null);  // since the previous line asked for a body
            if (cf.Rhs == null) {
//              var sw = EmitReturnExpr(w);
//              // get { return this._{0}; }
//              EmitThis(sw);
//              sw.Write("._{0}", cf.CompileName);
            }
            else {
              // TODO: CompileReturnBody(cf.Rhs, w, null);
            }
          }
        }
        else if (member is Field) {
          if (NeedsWrappersForInheritedFields) {
            var f = (Field) member;
            // every field is inherited
//            classWriter.DeclareField("_" + f.CompileName, false, false, f.Type, f.tok, DefaultValue(f.Type, errorWr, f.tok, true));
//            TargetWriter wSet;
//            var wGet = classWriter.CreateGetterSetter(IdName(f), f.Type, f.tok, false, true, member, out wSet);
            {
//              var sw = EmitReturnExpr(wGet);
              // get { return this._{0}; }
//              EmitThis(sw);
//              sw.Write("._{0}", f.CompileName);
            }
            {
              // set { this._{0} = value; }
//              EmitThis(wSet);
//              wSet.Write("._{0}", f.CompileName);
//              var sw = EmitAssignmentRhs(wSet);
//              EmitSetterParameter(sw);
            }
          }
          else {
            var f = (Field) member;
            AST.Expression rhs = null;
            if (!FieldsInTraits && f is ConstantField cf && cf.Rhs != null) {
              // TODO: TrExpr(cf.Rhs, w, false);
              //rhs = TrExpr()...;
              // TODO: classWriter.DeclareField(f.CompileName, false, true, f.Type, f.tok, rhs);
            }
            else {

              // TODO: classWriter.DeclareField(f.CompileName, false, false, f.Type, f.tok, DefaultValue(f.Type, errorWr, f.tok, true));
            }

            if (!FieldsInTraits) {
              // Create getters and setters for "traits" in languages that don't allow for non-final field declarations.
//              TargetWriter wSet;
//              var wGet = classWriter.CreateGetterSetter(IdName(f), f.Type, f.tok, false, true, member, out wSet);
              {
//                var sw = EmitReturnExpr(wGet);
                // get { return this.{0}; }
//                EmitThis(sw);
//                sw.Write(".{0}", f.CompileName);
              }
              {
                // set { this.{0} = value; }
//                EmitThis(wSet);
//                wSet.Write(".{0}", f.CompileName);
//                var sw = EmitAssignmentRhs(wSet);
//                EmitSetterParameter(sw);
              }
            }
          }
        }
        else if (member is Function) {
          var f = (Function) member;
          Contract.Assert(f.Body != null);
          // TODO CompileFunction(f, classWriter);
        }
        else if (member is Method) {
          var method = (Method) member;
          Contract.Assert(method.Body != null);
          // TODO CompileMethod(method, classWriter);
        }
        else {
          Contract.Assert(false); // unexpected member
        }
      }

      foreach (MemberDecl member in c.Members) {
        if (member is Field) {
          var f = (Field) member;
          if (f.IsGhost) {
            // emit nothing, but check for assumes
            // TODO
            // if (f is ConstantField cf && cf.Rhs != null) {
            //   var v = new CheckHasNoAssumes_Visitor(this, errorWr);
            //   v.Visit(cf.Rhs);
            // }
          }
          else if (!DafnyOptions.O.DisallowExterns && Attributes.Contains(f.Attributes, "extern")) {
            // emit nothing
          }
          else if (f is ConstantField) {
            // TODO
            // var cf = (ConstantField)f;
            // if (SupportsProperties || (c is NewtypeDecl && !cf.IsStatic)) {
            //   BlockTargetWriter wBody;
            //   if (c is NewtypeDecl && !cf.IsStatic) {
            //     // an instance field in a newtype needs to be modeled as a static function that takes a parameter,
            //     // because a newtype value is always represented as some existing type
            //     wBody = classWriter.CreateFunction(IdName(cf), new List<TypeParameter>(), new List<Formal>(), cf.Type, cf.tok, true, true, cf);
            //   } else if (cf.IsStatic) {
            //     wBody = classWriter.CreateGetter(IdName(cf), cf.Type, cf.tok, true, true, cf);
            //     Contract.Assert(wBody != null);  // since the previous line asked for a body
            //   } else if (c is TraitDecl) {
            //     wBody = classWriter.CreateGetter(IdName(cf), cf.Type, cf.tok, false, false, cf);
            //     Contract.Assert(wBody == null);  // since the previous line said not to create a body
            //   } else if (cf.Rhs == null) {
            //     // create a backing field, since this constant field may be assigned in constructors
            //     classWriter.DeclareField("_" + f.CompileName, false, false, f.Type, f.tok, DefaultValue(f.Type, errorWr, f.tok, true));
            //     wBody = classWriter.CreateGetter(IdName(cf), cf.Type, cf.tok, false, true, cf);
            //     Contract.Assert(wBody != null);  // since the previous line asked for a body
            //   } else {
            //     wBody = classWriter.CreateGetter(IdName(cf), cf.Type, cf.tok, false, true, cf);
            //     Contract.Assert(wBody != null);  // since the previous line asked for a body
            //   }
            //   if (wBody != null) {
            //     if (cf.Rhs != null) {
            //       CompileReturnBody(cf.Rhs, wBody, null);
            //     } else if (!cf.IsStatic) {
            //       var sw = EmitReturnExpr(wBody);
            //       EmitMemberSelect(EmitThis, cf, f.Type, internalAccess: true).EmitRead(sw);
            //     } else {
            //       EmitReturnExpr(DefaultValue(cf.Type, wBody, cf.tok, true), wBody);
            //     }
            //   }
            // } else {
            //   // If properties aren't supported, just use a field and hope
            //   // everyone plays nicely ...
            //   string rhs;
            //   if (cf.Rhs != null) {
            //     var w = new TargetWriter();
            //     TrExpr(cf.Rhs, w, false);
            //     rhs = w.ToString();
            //   } else {
            //     rhs = null;
            //   }
            //   if (!(c is TraitDecl && !FieldsInTraits) || cf.IsStatic) {
            //     classWriter.DeclareField(IdName(f), f.IsStatic, true, f.Type, f.tok, rhs);
            //   } else { // Constant fields in traits (Java interface) should be get methods.
            //     classWriter.CreateGetter(IdName(cf), cf.Type, cf.tok, false, false, cf);
            //   }
            // }
          }
          else if (c is TraitDecl && NeedsWrappersForInheritedFields) {
            // TODO
            // TargetWriter wSet;
            // var wGet = classWriter.CreateGetterSetter(IdName(f), f.Type, f.tok, f.IsStatic, false, member, out wSet);
            // Contract.Assert(wSet == null && wGet == null);  // since the previous line specified no body
          }
          else if (c is TraitDecl && !FieldsInTraits && !f.IsStatic) {
            // TODO
            // TargetWriter wSet;
            // classWriter.CreateGetterSetter(IdName(f), f.Type, f.tok, false, false, member, out wSet);
          }
          else {
            // TODO
            //classWriter.DeclareField(IdName(f), f.IsStatic, false, f.Type, f.tok, DefaultValue(f.Type, errorWr, f.tok, true));
          }
        }
        else if (member is Function) {
          var f = (Function) member;
          if (f.Body == null && !(c is TraitDecl && !f.IsStatic) &&
              !(!DafnyOptions.O.DisallowExterns && (Attributes.Contains(f.Attributes, "dllimport") ||
                                                    IncludeExternMembers &&
                                                    Attributes.Contains(f.Attributes, "extern")))) {
            // A (ghost or non-ghost) function must always have a body, except if it's an instance function in a trait.
            // TODO
            // if (Attributes.Contains(f.Attributes, "axiom") || (!DafnyOptions.O.DisallowExterns && Attributes.Contains(f.Attributes, "extern"))) {
            //   // suppress error message
            // } else {
            //   Error(f.tok, "Function {0} has no body", errorWr, f.FullName);
            // }
          }
          else if (f.IsGhost) {
            // TODO
            // nothing to compile, but we do check for assumes
            // if (f.Body == null) {
            //   Contract.Assert(c is TraitDecl && !f.IsStatic || Attributes.Contains(f.Attributes, "extern"));
            // } else {
            //   var v = new CheckHasNoAssumes_Visitor(this, errorWr);
            //   v.Visit(f.Body);
            // }
            //
            // if (Attributes.Contains(f.Attributes, "test")) {
            //   Error(f.tok, "Function {0} must be compiled to use the {{:test}} attribute", errorWr, f.FullName);
            // }
          }
          else if (c is TraitDecl && !f.IsStatic) {
            // TODO
            // var w = classWriter.CreateFunction(IdName(f), f.TypeArgs, f.Formals, f.ResultType, f.tok, false, false, f);
            // Contract.Assert(w == null);  // since we requested no body
          }
          else {
            // TODO
            //CompileFunction(f, classWriter);
          }
        }
        else if (member is Method) {
          var m = (Method) member;
          if (m.Body == null && !(c is TraitDecl && !m.IsStatic) &&
              !(!DafnyOptions.O.DisallowExterns && (Attributes.Contains(m.Attributes, "dllimport") ||
                                                    IncludeExternMembers &&
                                                    Attributes.Contains(m.Attributes, "extern")))) {
            // A (ghost or non-ghost) method must always have a body, except if it's an instance method in a trait.
            if (Attributes.Contains(m.Attributes, "axiom") ||
                (!DafnyOptions.O.DisallowExterns && Attributes.Contains(m.Attributes, "extern"))) {
              // suppress error message
            }
            else {
              Error(m.tok, "Method {0} has no body", errorWr, m.FullName);
            }
          }
          else if (m.IsGhost) {
            // nothing to compile, but we do check for assumes
            if (m.Body == null) {
              Contract.Assert(c is TraitDecl && !m.IsStatic);
            }
            else {
              // TODO
              // var v = new CheckHasNoAssumes_Visitor(this, errorWr);
              // v.Visit(m.Body);
            }
          }
          else if (c is TraitDecl && !m.IsStatic) {
            // TODO
            // var w = classWriter.CreateMethod(m, false);
            // Contract.Assert(w == null);  // since we requested no body
          }
          else {
            cd.members.Add(TrMethod(m));
          }
        }
        else {
          Contract.Assert(false);
          throw new cce.UnreachableException(); // unexpected member
        }
      }

      thisContext = null;
    }


    private AST.MethodDeclaration TrMethod(Method m) {
      Contract.Requires(errorWr != null);
      Contract.Requires(m != null);
      Contract.Requires(m.Body != null);

      AST.MethodDeclaration md = new AST.MethodDeclaration();
      md.name = m.Name;
      md.formals = new List<AST.VarDeclaration>();
      md.body = new AST.BlockStatement(new List<AST.Statement>());
      md.modifiers = "public";
      if (m.IsStatic) md.modifiers = "public static";

      if (m.Outs.Count == 0) md.returnType = new AST.SimpleType("void");
      else md.returnType = TrType(m.Outs.First().Type);

      foreach (MaybeFreeExpression e in m.Req) {
        md.clauses.Add(new AST.RequiresClause(TrExpr(e.E)));
      }

      Contract.Assert(results == null);
      results = new Dictionary<string,string>();
      if (m.Outs.Count == 1) {
        results.Add(m.Outs.First().Name, "\\result");
      } else {
        foreach (Formal f in m.Outs) {
          string name = f.Name;
          results.Add(name, "\\result." + name);
        }
      }

      foreach (MaybeFreeExpression e in m.Ens) {
        md.clauses.Add(new AST.EnsuresClause(TrExpr(e.E)));
      }

      results.Clear();
      results = null;
      
      //var w = cw.CreateMethod(m, !m.IsExtern(out _, out _));
      {
        // if (m.IsTailRecursive) {
        //   w = EmitTailCallStructure(m, w);
        // }
        // Coverage.Instrument(m.Body.Tok, $"entry to method {m.FullName}", w);

        int nonGhostOutsCount = 0;
        foreach (var p in m.Outs) {
          if (!p.IsGhost) {
            nonGhostOutsCount++;
          }
        }

        var useReturnStyleOuts = UseReturnStyleOuts(m, nonGhostOutsCount);
        foreach (var p in m.Outs) {
          if (!p.IsGhost) {
            // TODO DeclareLocalOutVar(IdName(p), p.Type, p.tok, DefaultValue(p.Type, w, p.tok, true), useReturnStyleOuts, w);
          }
        }

        // TODO w = EmitMethodReturns(m, w);

        if (m.Body == null) {
          Error(m.tok, "Method {0} has no body", errorWr, m.FullName);
        }
        else {
          Contract.Assert(enclosingMethod == null);
          enclosingMethod = m;
          md.body = (AST.BlockStatement)TrStmt(m.Body); // TODO
          // TODO: TrStmtList(m.Body.Body, w);
          Contract.Assert(enclosingMethod == m);
          enclosingMethod = null;
        }
      }

      // allow the Main method to be an instance method
      if (IsMain(m) && (!m.IsStatic || m.CompileName != "Main")) {
        // TODO
        //   w = CreateStaticMain(cw);
        //   if (!m.IsStatic) {
        //     var c = m.EnclosingClass;
        //     var typeArgs = c.TypeArgs.ConvertAll(tp => (Type)Type.Bool);
        //     var ty = new UserDefinedType(m.tok, c.Name, c, typeArgs);
        //     var wRhs = DeclareLocalVar("b", ty, m.tok, w);
        //     EmitNew(ty, m.tok, null, wRhs);
        //     w.WriteLine("b.{0}();", IdName(m));
        //   } else {
        //     w.WriteLine("{0}();", IdName(m));
        //   }
      }

      if (IsMain(m)) {
        md.name = "main";
        md.formals = new List<AST.VarDeclaration>();
        AST.Type t = new AST.ArrayType(new AST.SimpleType("String"), 1);
        AST.VarDeclaration v = new AST.VarDeclaration("args",t,null);
        md.formals.Add(v);
      }

      return md;
    }

    // protected class ClassWriter : IClassWriter {
    //   public readonly JavaASTCompiler Compiler;
    //   public readonly TargetWriter InstanceMemberWriter;
    //   public readonly TargetWriter StaticMemberWriter;
    //   public readonly TargetWriter CtorBodyWriter;
    //
    //   public ClassWriter(JavaASTCompiler compiler, TargetWriter instanceMemberWriter, TargetWriter ctorBodyWriter, BlockTargetWriter staticMemberWriter = null) {
    //     Contract.Requires(compiler != null);
    //     Contract.Requires(instanceMemberWriter != null);
    //     this.Compiler = compiler;
    //     this.InstanceMemberWriter = instanceMemberWriter;
    //     this.CtorBodyWriter = ctorBodyWriter;
    //     this.StaticMemberWriter = staticMemberWriter == null ? instanceMemberWriter : staticMemberWriter;
    //   }
    //
    //   public TargetWriter Writer(bool isStatic) {
    //     return isStatic ? StaticMemberWriter : InstanceMemberWriter;
    //   }
    //
    //   public BlockTargetWriter CreateConstructor(TopLevelDeclWithMembers c, List<TypeParameter> l){
    //     return Compiler.CreateConstructor(c, Writer(false), l);
    //   }
    //
    //   public BlockTargetWriter/*?*/ CreateMethod(Method m, bool createBody) {
    //     return Compiler.CreateMethod(m, createBody, Writer(m.IsStatic));
    //   }
    //   public BlockTargetWriter/*?*/ CreateFunction(string name, List<TypeParameter>/*?*/ typeArgs, List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member) {
    //     return Compiler.CreateFunction(name, typeArgs, formals, resultType, tok, isStatic, createBody, member, Writer(isStatic));
    //   }
    //
    //   public BlockTargetWriter/*?*/ CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member) {
    //     return Compiler.CreateGetter(name, resultType, tok, isStatic, createBody, Writer(isStatic));
    //   }
    //   public BlockTargetWriter/*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl/*?*/ member, out TargetWriter setterWriter) {
    //     return Compiler.CreateGetterSetter(name, resultType, tok, isStatic, createBody, out setterWriter, Writer(isStatic));
    //   }
    //   public void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs) {
    //     Compiler.DeclareField(name, isStatic, isConst, type, tok, rhs, this);
    //   }
    //   public TextWriter/*?*/ ErrorWriter() => InstanceMemberWriter;
    //
    //   public void Finish() { }
    // }

    protected BlockTargetWriter CreateGetter(string name, Type resultType, Bpl.IToken tok, bool isStatic,
      bool createBody, TargetWriter wr) {
      wr.Write("public {0}{1} get_{2}()", isStatic ? "static " : "", TypeName(resultType, wr, tok), name);
      if (createBody) {
        var w = wr.NewBlock("", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
        return w;
      }
      else {
        wr.WriteLine(";");
        return null;
      }
    }

    protected override void DeclareLocalVar(string name, Type /*?*/ type, Bpl.IToken /*?*/ tok, Expression rhs,
      bool inLetExprBody, TargetWriter wr) {
      if (type == null) {
        type = rhs.Type;
      }

      var w = DeclareLocalVar(name, type, tok, wr);
      TrExpr(rhs, w, inLetExprBody);
    }

    public BlockTargetWriter /*?*/ CreateGetterSetter(string name, Type resultType, Bpl.IToken tok, bool isStatic,
      bool createBody, out TargetWriter setterWriter, TargetWriter wr) {
      wr.Write("public {0}{1} get_{2}()", isStatic ? "static " : "", TypeName(resultType, wr, tok), name);
      BlockTargetWriter wGet = null;
      if (createBody) {
        wGet = wr.NewBlock("", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
      }
      else {
        wr.WriteLine(";");
      }

      wr.Write("public {0}void set_{1}({2} value)", isStatic ? "static " : "", name, TypeName(resultType, wr, tok));
      if (createBody) {
        setterWriter = wr.NewBlock("", null, BlockTargetWriter.BraceStyle.Newline,
          BlockTargetWriter.BraceStyle.Newline);
      }
      else {
        wr.WriteLine(";");
        setterWriter = null;
      }

      return wGet;
    }

    protected BlockTargetWriter CreateMethod(Method m, bool createBody, TargetWriter wr) {
      if (m.IsExtern(out _, out _) && (m.IsStatic || m is Constructor)) {
        // No need for an abstract version of a static method or a constructor
        return null;
      }

      string targetReturnTypeReplacement = null;
      int nonGhostOuts = 0;
      int nonGhostIndex = 0;
      for (int i = 0; i < m.Outs.Count; i++) {
        if (!m.Outs[i].IsGhost) {
          nonGhostOuts += 1;
          nonGhostIndex = i;
        }
      }

      if (nonGhostOuts == 1) {
        targetReturnTypeReplacement = TypeName(m.Outs[nonGhostIndex].Type, wr, m.Outs[nonGhostIndex].tok);
      }
      else if (nonGhostOuts > 1) {
        targetReturnTypeReplacement = DafnyTupleClassPrefix + nonGhostOuts;
      }

      var customReceiver = NeedsCustomReceiver(m);
      var receiverType = UserDefinedType.FromTopLevelDecl(m.tok, m.EnclosingClass);
      CreateSpecifications(m, wr);
      wr.Write("public {0}{1}", !createBody ? "abstract " : "", m.IsStatic || customReceiver ? "static " : "");
      if (m.TypeArgs.Count != 0) {
        wr.Write($"<{TypeParameters(m.TypeArgs)}> ");
      }

      wr.Write("{0} {1}", targetReturnTypeReplacement ?? "void", IdName(m));
      wr.Write("(");
      var nTypes = WriteRuntimeTypeDescriptorsFormals(m, m.TypeArgs, useAllTypeArgs: true, wr);
      var sep = nTypes > 0 ? ", " : "";
      if (customReceiver) {
        DeclareFormal(sep, "_this", receiverType, m.tok, true, wr);
        sep = ", ";
      }

      WriteFormals(sep, m.Ins, wr);
      if (!createBody) {
        wr.WriteLine(");");
        return null; // We do not want to write a function body, so instead of returning a BTW, we return null.
      }
      else {
        return wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
      }
    }


    public void CreateSpecifications(Method m, TargetWriter wr) {
      wr.WriteLine("//@// SPECS");
      foreach (MaybeFreeExpression e in m.Req) {
        // FIXME - what about labels, what about isFree
        wr.Write("//@ requires ");
        TrExpr(e.E, wr, false);
        wr.WriteLine(";");
      }

      bool isPure = true;
      // // TODO: m.Mod, m.Decreases
      foreach (MaybeFreeExpression e in m.Ens) {
        // FIXME - what about labels, what about isFree
        wr.Write("//@ ensures ");
        TrExpr(e.E, wr, false);
        wr.WriteLine(";");
      }

      if (isPure) {
        wr.WriteLine("//@ pure");
      }
    }


    protected override BlockTargetWriter EmitMethodReturns(Method m, BlockTargetWriter wr) {
      int nonGhostOuts = 0;
      foreach (var t in m.Outs) {
        if (t.IsGhost) continue;
        nonGhostOuts += 1;
        break;
      }

      if (!m.Body.Body.OfType<ReturnStmt>().Any() && (nonGhostOuts > 0 || m.IsTailRecursive)) {
        // If method has out parameters or is tail-recursive but no explicit return statement in Dafny
        var r = new TargetWriter(wr.IndentLevel);
        EmitReturn(m.Outs, r);
        wr.BodySuffix = r.ToString();
        wr = wr.NewBlock("if(true)"); // Ensure no unreachable error is thrown for the return statement
      }

      return wr;
    }

    protected BlockTargetWriter CreateConstructor(TopLevelDeclWithMembers c, TargetWriter wr, List<TypeParameter> l) {
      EmitSuppression(wr);
      wr.Write("public ");
      wr.Write(c.CompileName);
      wr.Write("(");
      var nTypes = WriteRuntimeTypeDescriptorsFormals(l, false, wr);
      var w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
      return w;
    }

    protected BlockTargetWriter /*?*/ CreateFunction(string name, List<TypeParameter> /*?*/ typeArgs,
      List<Formal> formals, Type resultType, Bpl.IToken tok, bool isStatic, bool createBody, MemberDecl member,
      TargetWriter wr) {
      if (member.IsExtern(out _, out _) && isStatic) {
        // No need for abstract version of static method
        return null;
      }

      var customReceiver = NeedsCustomReceiver(member);
      var receiverType = UserDefinedType.FromTopLevelDecl(member.tok, member.EnclosingClass);
      wr.Write("public {0}{1}", !createBody ? "abstract " : "", isStatic || customReceiver ? "static " : "");
      if (typeArgs != null && typeArgs.Count != 0) {
        wr.Write($"<{TypeParameters(typeArgs)}>");
        wr.Write($"{TypeName(resultType, wr, tok)} {name}(");
      }
      else if (isStatic && resultType.TypeArgs.Count > 0 && resultType.TypeArgs[0].IsTypeParameter) {
        string t = "";
        string n = "";
        SplitType(TypeName(resultType, wr, tok), out t, out n);
        wr.Write($"{t} {n} {name}(");
      }
      else {
        wr.Write($"{TypeName(resultType, wr, tok)} {name}(");
      }

      var sep = "";
      var argCount = 0;
      if (customReceiver) {
        DeclareFormal(sep, "_this", receiverType, tok, true, wr);
        sep = ", ";
        argCount++;
      }

      argCount += WriteRuntimeTypeDescriptorsFormals(typeArgs, useAllTypeArgs: true, wr, sep);
      if (argCount > 0) {
        sep = ", ";
      }

      argCount += WriteFormals(sep, formals, wr);
      if (!createBody) {
        wr.WriteLine(");");
        return null; // We do not want to write a function body, so instead of returning a BTW, we return null.
      }
      else {
        BlockTargetWriter w;
        if (argCount > 1) {
          w = wr.NewBlock(")", null, BlockTargetWriter.BraceStyle.Newline, BlockTargetWriter.BraceStyle.Newline);
        }
        else {
          w = wr.NewBlock(")");
        }

        return w;
      }
    }

    private void SplitType(string s, out string t, out string n) {
      string pat = @"([^<]+)(<.*>)";
      Regex r = new Regex(pat);
      Match m = r.Match(s);
      if (m.Groups.Count < 2) {
        n = s;

        t = null;
      }
      else {
        n = m.Groups[1].Captures[0].Value;
        t = m.Groups[2].Captures[0].Value;
      }
    }

    // protected void DeclareField(string name, bool isStatic, bool isConst, Type type, Bpl.IToken tok, string rhs, ClassWriter cw) {
    //   if (isStatic){
    //     var r = RemoveParams((rhs != null) ? rhs : DefaultValue(type, cw.StaticMemberWriter, tok));
    //     var t = RemoveParams(TypeName(type, cw.StaticMemberWriter, tok));
    //     cw.StaticMemberWriter.WriteLine($"public static {t} {name} = {r};");
    //   }
    //   else{
    //     Contract.Assert(cw.CtorBodyWriter != null, "Unexpected instance field");
    //     cw.InstanceMemberWriter.WriteLine("public {0} {1};", TypeName(type, cw.InstanceMemberWriter, tok), name);
    //     cw.CtorBodyWriter.WriteLine("this.{0} = {1};", name, rhs ?? DefaultValue(type, cw.CtorBodyWriter, tok, inAutoInitContext: true));
    //   }
    // }

    private string RemoveParams(string s) {
      return Regex.Replace(s, @"<.>", "");
    }

    private void EmitSuppression(TextWriter wr) {
      wr.WriteLine("@SuppressWarnings({\"unchecked\", \"deprecation\"})");
    }

    string TypeParameters(List<TypeParameter> targs) {
      Contract.Requires(cce.NonNullElements(targs));
      Contract.Ensures(Contract.Result<string>() != null);

      return Util.Comma(targs, tp => IdName(tp));
    }

    protected override string TypeName(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl /*?*/ member = null) {
      return TypeName(type, wr, tok, boxed: false, member);
    }

    private string BoxedTypeName(Type type, TextWriter wr, Bpl.IToken tok) {
      return TypeName(type, wr, tok, boxed: true);
    }

    private string BoxedTypeNames(List<Type> types, TextWriter wr, Bpl.IToken tok) {
      return Util.Comma(types, t => BoxedTypeName(t, wr, tok));
    }

    protected override string TypeArgumentName(Type type, TextWriter wr, Bpl.IToken tok) {
      return BoxedTypeName(type, wr, tok);
    }

    private string TypeName(Type type, TextWriter wr, Bpl.IToken tok, bool boxed, MemberDecl /*?*/ member = null) {
      Contract.Ensures(Contract.Result<string>() != null);
      Contract.Assume(type != null); // precondition; this ought to be declared as a Requires in the superclass

      var xType = type.NormalizeExpand();
      if (xType is TypeProxy) {
        // unresolved proxy; just treat as ref, since no particular type information is apparently needed for this type
        return "Object";
      }

      if (xType is BoolType) {
        return boxed ? "Boolean" : "boolean";
      }
      else if (xType is CharType) {
        return boxed ? "Character" : "char";
      }
      else if (xType is IntType || xType is BigOrdinalType) {
        return "java.math.BigInteger";
      }
      else if (xType is RealType) {
        return DafnyBigRationalClass;
      }
      else if (xType is BitvectorType) {
        var t = (BitvectorType) xType;
        return t.NativeType != null ? GetNativeTypeName(t.NativeType, boxed) : "java.math.BigInteger";
      }
      else if (member == null && xType.AsNewtype != null) {
        var nativeType = xType.AsNewtype.NativeType;
        if (nativeType != null) {
          return GetNativeTypeName(nativeType, boxed);
        }

        return TypeName(xType.AsNewtype.BaseType, wr, tok, boxed);
      }
      else if (xType.IsObjectQ) {
        return "Object";
      }
      else if (xType.IsArrayType) {
        ArrayClassDecl at = xType.AsArrayType;
        Contract.Assert(at != null); // follows from type.IsArrayType
        Type elType = UserDefinedType.ArrayElementType(xType);
        return ArrayTypeName(elType, at.Dims, wr, tok);
      }
      else if (xType is UserDefinedType) {
        var udt = (UserDefinedType) xType;
        var s = FullTypeName(udt, member);
        if (s.Equals("string")) {
          return "String";
        }

        var cl = udt.ResolvedClass;
        bool isHandle = true;
        if (cl != null && Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return boxed ? "Long" : "long";
        }
        else if (cl is TupleTypeDecl tupleDecl) {
          s = DafnyTupleClass(tupleDecl.TypeArgs.Count);
        }
        else if (DafnyOptions.O.IronDafny &&
                 !(xType is ArrowType) &&
                 cl != null &&
                 cl.Module != null &&
                 !cl.Module.IsDefaultModule) {
          s = cl.FullCompileName;
        }

        // When accessing a static member, leave off the type arguments
        var typeArgs = member != null ? new List<Type>() : udt.TypeArgs;
        return TypeName_UDT(s, typeArgs, wr, udt.tok);
      }
      else if (xType is SetType) {
        Type argType = ((SetType) xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of set<TRAIT> is not supported; consider introducing a ghost", wr);
        }

        return DafnySetClass + "<" + BoxedTypeName(argType, wr, tok) + ">";
      }
      else if (xType is SeqType) {
        Type argType = ((SeqType) xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of seq<TRAIT> is not supported; consider introducing a ghost", wr);
        }

        return DafnySeqClass + "<" + BoxedTypeName(argType, wr, tok) + ">";

      }
      else if (xType is MultiSetType) {
        Type argType = ((MultiSetType) xType).Arg;
        if (ComplicatedTypeParameterForCompilation(argType)) {
          Error(tok, "compilation of multiset<TRAIT> is not supported; consider introducing a ghost", wr);
        }

        return DafnyMultiSetClass + "<" + BoxedTypeName(argType, wr, tok) + ">";
      }
      else if (xType is MapType) {
        Type domType = ((MapType) xType).Domain;
        Type ranType = ((MapType) xType).Range;
        if (ComplicatedTypeParameterForCompilation(domType) || ComplicatedTypeParameterForCompilation(ranType)) {
          Error(tok, "compilation of map<TRAIT, _> or map<_, TRAIT> is not supported; consider introducing a ghost",
            wr);
        }

        return DafnyMapClass + "<" + BoxedTypeName(domType, wr, tok) + "," + BoxedTypeName(ranType, wr, tok) + ">";
      }
      else {
        Contract.Assert(false);
        throw new cce.UnreachableException(); // unexpected type
      }
    }

    string ArrayTypeName(Type elType, int dims, TextWriter wr, Bpl.IToken tok) {
      if (dims > 1) {
        arrays.Add(dims);
        return $"{DafnyMultiArrayClass(dims)}<{BoxedTypeName(elType, wr, tok)}>";
      }
      else if (elType.IsTypeParameter) {
        return "java.lang.Object";
      }
      else {
        return $"{TypeName(elType, wr, tok)}[]";
      }
    }

    protected string CollectionTypeUnparameterizedName(CollectionType ct) {
      if (ct is SeqType) {
        return DafnySeqClass;
      }
      else if (ct is SetType) {
        return DafnySetClass;
      }
      else if (ct is MultiSetType) {
        return DafnyMultiSetClass;
      }
      else if (ct is MapType) {
        return DafnyMapClass;
      }
      else {
        Contract.Assert(false); // unexpected collection type
        throw new cce.UnreachableException(); // to please the compiler
      }
    }

    protected override string FullTypeName(UserDefinedType udt, MemberDecl /*?*/ member = null) {
      Contract.Assume(udt != null); // precondition; this ought to be declared as a Requires in the superclass
      if (udt is ArrowType) {
        functions.Add(udt.TypeArgs.Count - 1);
        return DafnyFunctionIface(udt.TypeArgs.Count - 1);
      }

      string qualification;
      if (member != null && member.IsExtern(out qualification, out _) && qualification != null) {
        return qualification;
      }

      var cl = udt.ResolvedClass;
      if (cl == null) {
        return IdProtect(udt.CompileName);
      }
      else if (cl is TupleTypeDecl tupleDecl) {
        return DafnyTupleClass(tupleDecl.TypeArgs.Count);
      }
      else if (cl.Module.CompileName == ModuleName || cl.Module.IsDefaultModule) {
        return IdProtect(cl.CompileName);
      }
      else {
        return IdProtect(cl.Module.CompileName) + "." + IdProtect(cl.CompileName);
      }
    }

    protected override string TypeNameArrayBrackets(int dims) {
      var name = "[";
      for (int i = 1; i < dims; i++) {
        name += "][";
      }

      return name + "]";
    }

    protected override bool DeclareFormal(string prefix, string name, Type type, Bpl.IToken tok, bool isInParam,
      TextWriter wr) {
      if (!isInParam) return false;
      wr.Write($"{prefix}{TypeName(type, wr, tok)} {name}");
      return true;
    }

    protected override string TypeName_UDT(string fullCompileName, List<Type> typeArgs, TextWriter wr, Bpl.IToken tok) {
      Contract.Assume(fullCompileName !=
                      null); // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(typeArgs != null); // precondition; this ought to be declared as a Requires in the superclass
      string s = IdProtect(fullCompileName);
      if (typeArgs.Count != 0) {
        if (typeArgs.Exists(ComplicatedTypeParameterForCompilation)) {
          Error(tok, "compilation does not support trait types as a type parameter; consider introducing a ghost", wr);
        }

        s += "<" + BoxedTypeNames(typeArgs, wr, tok) + ">";
      }

      return s;
    }

    protected string TypeName_UDT(string fullCompileName, List<Type> inArgs, Type outArgs, TextWriter wr,
      Bpl.IToken tok) {
      Contract.Assume(fullCompileName !=
                      null); // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(inArgs != null); // precondition; this ought to be declared as a Requires in the superclass
      Contract.Assume(outArgs != null); // precondition; this ought to be declared as a Requires in the superclass
      string s = IdProtect(fullCompileName);
      s += "<";
      if (inArgs.Count > 1) {
        if (inArgs.Exists(ComplicatedTypeParameterForCompilation)) {
          Error(tok, "compilation does not support trait types as a type parameter; consider introducing a ghost", wr);
        }

        s += DafnyTupleClass(inArgs.Count) + "<" + BoxedTypeNames(inArgs, wr, tok) + ">";
        tuples.Add(inArgs.Count);
      }
      else {
        if (inArgs.Exists(ComplicatedTypeParameterForCompilation)) {
          Error(tok, "compilation does not support trait types as a type parameter; consider introducing a ghost", wr);
        }

        s += "" + BoxedTypeNames(inArgs, wr, tok) + "";
      }

      if (outArgs != null) {
        if (inArgs.Count > 0) {
          s += ", ";
        }

        s += BoxedTypeName(outArgs, wr, tok) + "";
      }

      s += ">";
      return s;
    }

    // We write an extern class as a base class that the actual extern class
    // needs to extend, so the extern methods and functions need to be abstract
    // in the base class
    protected override bool IncludeExternMembers {
      get => true;
    }

    //
    // An example to show how type parameters are dealt with:
    //
    //   class Class<T /* needs zero initializer */, U /* does not */> {
    //     private String sT; // type descriptor for T
    //
    //     // Fields are assigned in the constructor because some will
    //     // depend on a type parameter
    //     public T t;
    //     public U u;
    //
    //     public Class(String sT) {
    //       this.sT = sT;
    //       this.t = dafny.Helpers.getDefault(sT);
    //       // Note: The field must be assigned a real value before being read!
    //       this.u = null;
    //     }
    //
    //     public __ctor(U u) {
    //       this.u = u;
    //     }
    //   }
    //
    protected override IClassWriter CreateClass(string name, bool isExtern, string /*?*/ fullPrintName,
      List<TypeParameter> /*?*/ typeParameters, List<Type> /*?*/ superClasses, Bpl.IToken tok, TargetWriter wr) {
      return null;
    }

    private void EmitTypeMethod(string typeName, List<TypeParameter> typeParams, List<TypeParameter> usedTypeParams,
      string /*?*/ initializer, TargetWriter wr) {
      var typeParamString = "";
      if (typeParams != null && typeParams.Count != 0) {
        typeParamString = $"<{TypeParameters(typeParams)}>";
      }

      var typeDescriptorCast = $"({TypeClass}<{typeName}{typeParamString}>) ({TypeClass}<?>)";
      var typeDescriptorExpr = $"{TypeClass}.referenceWithInitializer({typeName}.class, () -> {initializer ?? "null"})";
      if (usedTypeParams == null || usedTypeParams.Count == 0) {
        wr.WriteLine($"private static final {TypeClass}<{typeName}> _TYPE = {typeDescriptorExpr};");
      }

      wr.Write($"public static {typeParamString}{TypeClass}<{typeName}{typeParamString}> _type(");
      if (usedTypeParams != null) {
        wr.Write(Util.Comma(usedTypeParams,
          tp => $"{TypeClass}<{IdName(tp)}> {FormatTypeDescriptorVariable(tp.CompileName)}"));
      }

      var wTypeMethodBody = wr.NewBigBlock(")", "");
      if (usedTypeParams == null || usedTypeParams.Count == 0) {
        wTypeMethodBody.WriteLine($"return {typeDescriptorCast} _TYPE;");
      }
      else {
        wTypeMethodBody.WriteLine($"return {typeDescriptorCast} {typeDescriptorExpr};");
      }
    }

    private string CastIfSmallNativeType(Type t) {
      var nt = AsNativeType(t);
      return nt == null ? "" : CastIfSmallNativeType(nt);
    }

    private string CastIfSmallNativeType(NativeType nt) {
      switch (AsJavaNativeType(nt)) {
        case JavaNativeType.Byte: return "(byte) ";
        case JavaNativeType.Short: return "(short) ";
        default: return "";
      }
    }

    protected override void EmitLiteralExpr(TextWriter wr, LiteralExpr e) {
      if (e is StaticReceiverExpr) {
        wr.Write(TypeName(e.Type, wr, e.tok));
      }
      else if (e.Value == null) {
        wr.Write($"({TypeName(e.Type, wr, e.tok)}) null");
      }
      else if (e.Value is bool value) {
        wr.Write(value ? "true" : "false");
      }
      else if (e is CharLiteralExpr) {
        wr.Write($"'{(string) e.Value}'");
      }
      else if (e is StringLiteralExpr str) {
        wr.Write($"{DafnySeqClass}.asString(");
        TrStringLiteral(str, wr);
        wr.Write(")");
      }
      else if (AsNativeType(e.Type) is NativeType nt) {
        EmitNativeIntegerLiteral((BigInteger) e.Value, nt, wr);
      }
      else if (e.Value is BigInteger i) {
        if (i.IsZero) {
          wr.Write("java.math.BigInteger.ZERO");
        }
        else if (i.IsOne) {
          wr.Write("java.math.BigInteger.ONE");
        }
        else if (long.MinValue <= i && i <= long.MaxValue) {
          wr.Write($"java.math.BigInteger.valueOf({i}L)");
        }
        else {
          wr.Write($"new java.math.BigInteger(\"{i}\")");
        }
      }
      else if (e.Value is Basetypes.BigDec n) {
        if (0 <= n.Exponent) {
          wr.Write($"new {DafnyBigRationalClass}(new java.math.BigInteger(\"{n.Mantissa}");
          for (int j = 0; j < n.Exponent; j++) {
            wr.Write("0");
          }

          wr.Write("\"), java.math.BigInteger.ONE)");
        }
        else {
          wr.Write($"new {DafnyBigRationalClass}(");
          wr.Write($"new java.math.BigInteger(\"{n.Mantissa}\")");
          wr.Write(", new java.math.BigInteger(\"1");
          for (int j = n.Exponent; j < 0; j++) {
            wr.Write("0");
          }

          wr.Write("\"))");
        }
      }
      else {
        Contract.Assert(false);
        throw new cce.UnreachableException(); // unexpected literal
      }
    }

    protected override void EmitStringLiteral(string str, bool isVerbatim, TextWriter wr) {
      if (!isVerbatim) {
        wr.Write($"\"{str}\"");
      }
      else {
        //TODO: This is taken from Go and JS since Java doesn't have raw string literals, modify and make better if possible.
        var n = str.Length;
        wr.Write("\"");
        for (var i = 0; i < n; i++) {
          if (str[i] == '\"' && i + 1 < n && str[i + 1] == '\"') {
            wr.Write("\\\"");
            i++;
          }
          else if (str[i] == '\\') {
            wr.Write("\\\\");
          }
          else if (str[i] == '\n') {
            wr.Write("\\n");
          }
          else if (str[i] == '\r') {
            wr.Write("\\r");
          }
          else {
            wr.Write(str[i]);
          }
        }

        wr.Write("\"");
      }
    }

    void EmitNativeIntegerLiteral(BigInteger value, NativeType nt, TextWriter wr) {
      GetNativeInfo(nt.Sel, out var name, out var literalSuffix, out _);
      var intValue = value;
      if (intValue > long.MaxValue) {
        // The value must be a 64-bit unsigned integer, since it has a native
        // type and unsigned long is the biggest native type
        Contract.Assert(intValue <= ulong.MaxValue);

        // Represent the value as a signed 64-bit integer
        intValue -= ulong.MaxValue + BigInteger.One;
      }
      else if (nt.Sel == NativeType.Selection.UInt && intValue > int.MaxValue) {
        // Represent the value as a signed 32-bit integer
        intValue -= uint.MaxValue + BigInteger.One;
      }

      wr.Write($"{CastIfSmallNativeType(nt)}{intValue}{literalSuffix}");
    }

    protected string GetNativeDefault(NativeType nt) {
      switch (AsJavaNativeType(nt)) {
        case JavaNativeType.Byte: return "(byte) 0";
        case JavaNativeType.Short: return "(short) 0";
        case JavaNativeType.Int: return "0";
        case JavaNativeType.Long: return "0L";
        default:
          Contract.Assert(false); // unexpected native type
          throw new cce.UnreachableException(); // to please the compiler
      }
    }

    protected override void GetNativeInfo(NativeType.Selection sel, out string name, out string literalSuffix,
      out bool needsCastAfterArithmetic) {
      literalSuffix = "";
      needsCastAfterArithmetic = false;
      switch (AsJavaNativeType(sel)) {
        case JavaNativeType.Byte:
          name = "byte";
          needsCastAfterArithmetic = true;
          break;
        case JavaNativeType.Short:
          name = "short";
          needsCastAfterArithmetic = true;
          break;
        case JavaNativeType.Int:
          name = "int";
          break;
        case JavaNativeType.Long:
          name = "long";
          literalSuffix = "L";
          break;
        default:
          Contract.Assert(false); // unexpected native type
          throw new cce.UnreachableException(); // to please the compiler
      }
    }

    private string GetNativeTypeName(NativeType nt, bool boxed = false) {
      return boxed ? GetBoxedNativeTypeName(nt) : base.GetNativeTypeName(nt);
    }

    private string GetBoxedNativeTypeName(NativeType nt) {
      switch (AsJavaNativeType(nt)) {
        case JavaNativeType.Byte: return "Byte";
        case JavaNativeType.Short: return "Short";
        case JavaNativeType.Int: return "Integer";
        case JavaNativeType.Long: return "Long";
        default:
          Contract.Assert(false); // unexpected native type
          throw new cce.UnreachableException(); // to please the compiler
      }
    }

    // Note the (semantically iffy) distinction between a *primitive type*,
    // being one of the eight Java primitive types, and a NativeType, which can
    // only be one of the integer types.
    private bool IsJavaPrimitiveType(Type type) {
      return type.IsBoolType || type.IsCharType || AsNativeType(type) != null;
    }

    protected override void EmitThis(TargetWriter wr) {
      var custom =
        (enclosingMethod != null && enclosingMethod.IsTailRecursive) ||
        (enclosingFunction != null && enclosingFunction.IsTailRecursive) ||
        thisContext is NewtypeDecl;
      wr.Write(custom ? "_this" : "this");
    }

    protected override void DeclareLocalVar(string name, Type /*?*/ type, Bpl.IToken /*?*/ tok, bool leaveRoomForRhs,
      string /*?*/ rhs, TargetWriter wr) {
      if (type != null && type.AsArrayType != null) {
        arrays.Add(type.AsArrayType.Dims);
      }

      if (type.IsDatatype && type.AsDatatype is TupleTypeDecl) {
        tuples.Add(type.AsDatatype.TypeArgs.Count);
      }

      if (type.IsTypeParameter) {
        EmitSuppression(wr);
      }

      wr.Write("{0} {1}", type != null ? TypeName(type, wr, tok) : "Object", name);
      if (leaveRoomForRhs) {
        Contract.Assert(rhs == null); // follows from precondition
      }
      else if (rhs != null) {
        wr.WriteLine($" = {rhs};");
      }
      else if (type.IsIntegerType) {
        wr.WriteLine(" = java.math.BigInteger.ZERO;");
      }
      else {
        wr.WriteLine(";");
      }
    }

    protected override void DeclareLocalVar(string name, Type /*?*/ type, Bpl.IToken /*?*/ tok, bool leaveRoomForRhs,
      string /*?*/ rhs, TargetWriter wr, Type t) {
      DeclareLocalVar(name, t, tok, leaveRoomForRhs, rhs, wr);
    }

    protected override void EmitCollectionDisplay(CollectionType ct, Bpl.IToken tok, List<Expression> elements,
      bool inLetExprBody, TargetWriter wr) {
      if (elements.Count == 0) {
        wr.Write($"{CollectionTypeUnparameterizedName(ct)}.<{BoxedTypeName(ct.Arg, wr, tok)}> empty(");
        if (ct is SeqType) {
          wr.Write(TypeDescriptor(ct.Arg, wr, tok));
        }

        wr.Write(")");
        return;
      }

      wr.Write($"{CollectionTypeUnparameterizedName(ct)}.of(");
      string sep = "";
      if (ct is SeqType && !IsJavaPrimitiveType(ct.Arg)) {
        wr.Write(TypeDescriptor(ct.Arg, wr, tok));
        sep = ", ";
      }

      foreach (Expression e in elements) {
        wr.Write(sep);
        TrExpr(e, wr, inLetExprBody);
        sep = ", ";
      }

      wr.Write(")");
    }

    protected override void EmitMapDisplay(MapType mt, Bpl.IToken tok, List<ExpressionPair> elements,
      bool inLetExprBody, TargetWriter wr) {
      wr.Write("new dafny.DafnyMap() {{{{\n");
      foreach (ExpressionPair p in elements) {
        wr.Write("put(");
        TrExpr(p.A, wr, inLetExprBody);
        wr.Write(", ");
        TrExpr(p.B, wr, inLetExprBody);
        wr.Write(");\n");
      }

      wr.Write("}}}}");
    }

    protected override void GetSpecialFieldInfo(SpecialField.ID id, object idParam, out string compiledName,
      out string preString, out string postString) {
      compiledName = "";
      preString = "";
      postString = "";
      switch (id) {
        case SpecialField.ID.UseIdParam:
          compiledName = IdProtect((string) idParam);
          break;
        case SpecialField.ID.ArrayLength:
        case SpecialField.ID.ArrayLengthInt:
          if (idParam == null) {
            // Works on both fixed array types like array<int> (=> BigInteger[])
            // or generic array types like array<A> (=> Object) and (unlike most
            // of java.lang.reflect.Array) is fast
            preString = "java.lang.reflect.Array.getLength(";
            postString = ")";
          }
          else {
            compiledName = "dim" + (int) idParam;
          }

          if (id == SpecialField.ID.ArrayLength) {
            preString = "java.math.BigInteger.valueOf(" + preString;
            postString = postString + ")";
          }

          break;
        case SpecialField.ID.Floor:
          compiledName = "toBigInteger()";
          break;
        case SpecialField.ID.IsLimit:
          preString = "dafny.BigOrdinal.IsLimit(";
          postString = ")";
          break;
        case SpecialField.ID.IsSucc:
          preString = "dafny.BigOrdinal.IsSucc(";
          postString = ")";
          break;
        case SpecialField.ID.Offset:
          preString = "dafny.BigOrdinal.Offset(";
          postString = ")";
          break;
        case SpecialField.ID.IsNat:
          preString = "dafny.BigOrdinal.IsNat(";
          postString = ")";
          break;
        case SpecialField.ID.Keys:
          compiledName = "dafnyKeySet()";
          break;
        case SpecialField.ID.Values:
          compiledName = "dafnyValues()";
          break;
        case SpecialField.ID.Items:
          compiledName = "dafnyEntrySet()";
          break;
        case SpecialField.ID.Reads:
          compiledName = "_reads";
          break;
        case SpecialField.ID.Modifies:
          compiledName = "_modifies";
          break;
        case SpecialField.ID.New:
          compiledName = "_new";
          break;
        default:
          Contract.Assert(false); // unexpected ID
          break;
      }
    }

    protected override ILvalue EmitMemberSelect(Action<TargetWriter> obj, MemberDecl member, Type expectedType,
      bool internalAccess = false) {
      if (member.EnclosingClass is TraitDecl && !member.IsStatic) {
        return new GetterSetterLvalue(obj, IdName(member));
      }
      else if (member is ConstantField) {
        return SuffixLvalue(obj, $".{member.CompileName}");
      }
      else if (member is SpecialField sf) {
        GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, out var compiledName, out _, out _);
        if (compiledName.Length != 0) {
          if (member.EnclosingClass is DatatypeDecl) {
            return new GetterSetterLvalue(obj, getter: compiledName, setter: null);
          }
          else {
            return SuffixLvalue(obj, $".{compiledName}");
          }
        }
        else {
          // Assume it's already handled by the caller
          return SimpleLvalue(obj);
        }
      }
      else if (member is Function) {
        return SuffixLvalue(obj, $"::{IdName(member)}");
      }
      else {
        return SuffixLvalue(obj, $".{IdName(member)}");
      }
    }

    // FIXME This is a bit sketchy: Rather than encapsulating the idea of an
    // lvalue, both EmitRead() and EmitWrite() assume (as does
    // EmitMemberSelect()) that the member has already been written and we need
    // only write the part starting with the period.  Cleaning up this logic
    // would require reworking the way EmitMemberSelect() is called.
    private class GetterSetterLvalue : ILvalue {
      private readonly Action<TargetWriter> Object;
      private readonly string Getter;

      private readonly string /*?*/
        Setter;

      public GetterSetterLvalue(Action<TargetWriter> obj, string name) {
        this.Object = obj;
        this.Getter = $"get_{name}";
        this.Setter = $"set_{name}";
      }

      public GetterSetterLvalue(Action<TargetWriter> obj, string getter, string /*?*/ setter) {
        this.Object = obj;
        this.Getter = getter;
        this.Setter = setter;
      }

      public void EmitRead(TargetWriter wr) {
        Object(wr);
        wr.Write($".{Getter}()");
      }

      public TargetWriter EmitWrite(TargetWriter wr) {
        Contract.Assert(Setter != null, "Unexpected write to read-only property");

        Object(wr);
        wr.Write($".{Setter}(");
        var w = wr.Fork();
        wr.WriteLine(");");
        return w;
      }
    }

    protected override void EmitConstructorCheck(string source, DatatypeCtor ctor, TargetWriter wr) {
      wr.Write($"{source}.is_{ctor.CompileName}()");
    }

    protected override string TypeName_Companion(Type type, TextWriter wr, Bpl.IToken tok, MemberDecl member) {
      if (type is UserDefinedType udt && udt.ResolvedClass is TraitDecl) {
        string s = IdProtect(udt.FullCompanionCompileName);
        Contract.Assert(udt.TypeArgs.Count == 0); // traits have no type parameters
        return s;
      }
      else {
        return TypeName(type, wr, tok, member);
      }
    }

    protected override TargetWriter EmitArraySelect(List<string> indices, Type elmtType, TargetWriter wr) {
      Contract.Assert(indices != null && 1 <= indices.Count); // follows from precondition
      List<TargetWriter> wIndices;
      var w = EmitArraySelect(indices.Count, out wIndices, elmtType, wr);
      for (int i = 0; i < indices.Count; i++) {
        if (!int.TryParse(indices[i], out _)) {
          wIndices[i].Write($"{DafnyHelpersClass}.toInt({indices[i]})");
        }
        else {
          wIndices[i].Write(indices[i]);
        }
      }

      return w;
    }

     protected override TargetWriter EmitArraySelect(List<Expression> indices, Type elmtType, bool inLetExprBody,
       TargetWriter wr) {
    //   Contract.Assert(indices != null && 1 <= indices.Count); // follows from precondition
    //   List<TargetWriter> wIndices;
    //   var w = EmitArraySelect(indices.Count, out wIndices, elmtType, wr);
    //
    //   for (int i = 0; i < indices.Count; i++) {
    //     TrParenExprAsInt(indices[i], wIndices[i], inLetExprBody);
    //   }
    //
    //   return w;
        return null;
     }

    private TargetWriter EmitArraySelect(int dimCount, out List<TargetWriter> wIndices, Type elmtType,
      TargetWriter wr) {
      wIndices = new List<TargetWriter>();
      TargetWriter w;
      if (dimCount == 1) {
        if (elmtType.IsTypeParameter) {
          wr.Write($"{FormatTypeDescriptorVariable(elmtType.AsTypeParameter)}.getArrayElement(");
          w = wr.Fork();
          wr.Write(", ");
          wIndices.Add(wr.Fork());
          wr.Write(")");
        }
        else {
          w = wr.Fork();
          wr.Write("[");
          wIndices.Add(wr.Fork());
          wr.Write("]");
        }
      }
      else {
        if (elmtType.IsTypeParameter) {
          w = wr.Fork();
          wr.Write(".get(");
          for (int i = 0; i < dimCount; i++) {
            if (i > 0) {
              wr.Write(", ");
            }

            wIndices.Add(wr.Fork());
          }

          wr.Write(")");
        }
        else {
          wr.Write($"(({TypeName(elmtType, wr, Bpl.Token.NoToken)}{Util.Repeat("[]", dimCount)}) ((");
          w = wr.Fork();
          wr.Write(").elmts))");
          for (int i = 0; i < dimCount; i++) {
            wr.Write("[");
            wIndices.Add(wr.Fork());
            wr.Write("]");
          }
        }
      }

      return w;
    }

    // TODO: Generalize the EmitArraySelectAsLvalue API to be rid of this duplication
    protected override TargetWriter EmitArrayUpdate(List<string> indices, string rhs, Type elmtType, TargetWriter wr) {
      TargetWriter w;
      if (indices.Count == 1) {
        if (elmtType.IsTypeParameter) {
          wr.Write($"{FormatTypeDescriptorVariable(elmtType.AsTypeParameter)}.setArrayElement(");
          w = wr.Fork();
          wr.Write($", {DafnyHelpersClass}.toInt({indices[0]}), {rhs})");
        }
        else {
          w = wr.Fork();
          wr.Write($"[{DafnyHelpersClass}.toInt({indices[0]})] = {rhs}");
        }
      }
      else {
        if (elmtType.IsTypeParameter) {
          w = wr.Fork();
          wr.Write($".set({Util.Comma(indices, ix => $"{DafnyHelpersClass}.toInt({ix})")}, {rhs})");
        }
        else {
          wr.Write($"(({TypeName(elmtType, wr, Bpl.Token.NoToken)}{Util.Repeat("[]", indices.Count)}) (");
          w = wr.Fork();
          wr.Write($").elmts){Util.Comma("", indices, ix => $"[{DafnyHelpersClass}.toInt({ix})]")} = {rhs}");
        }
      }

      return w;
    }

    protected override ILvalue EmitArraySelectAsLvalue(string array, List<string> indices, Type elmtType) {
      if (elmtType.IsTypeParameter) {
        return new GenericArrayElementLvalue(this, array, indices, elmtType.AsTypeParameter);
      }
      else {
        return SimpleLvalue(wr => {
          var wArray = EmitArraySelect(indices, elmtType, wr);
          wArray.Write(array);
        });
      }
    }

    private class GenericArrayElementLvalue : ILvalue {
      private readonly JavaASTCompiler Compiler;
      private readonly string Array;
      private readonly List<string> Indices;
      private readonly TypeParameter ElmtTypeParameter;

      public GenericArrayElementLvalue(JavaASTCompiler compiler, string array, List<string> indices,
        TypeParameter elmtTypeParameter) {
        Compiler = compiler;
        Array = array;
        Indices = indices;
        ElmtTypeParameter = elmtTypeParameter;
      }

      public void EmitRead(TargetWriter wr) {
        var wArray = Compiler.EmitArraySelect(Indices, new UserDefinedType(ElmtTypeParameter), wr);
        wArray.Write(Array);
      }

      public TargetWriter EmitWrite(TargetWriter wr) {
        TargetWriter w;
        if (Indices.Count == 1) {
          wr.Write($"{FormatTypeDescriptorVariable(ElmtTypeParameter)}.setArrayElement({Array}, ");
          w = wr.Fork();
          wr.Write(")");
        }
        else {
          wr.Write($"{Array}.set({Util.Comma("", Indices, ix => $"[{DafnyHelpersClass}.toInt({ix})]")}), ");
          w = wr.Fork();
          wr.Write(")");
        }

        return w;
      }
    }

     protected override void EmitSeqSelectRange(Expression source, Expression lo, Expression hi, bool fromArray,
       bool inLetExprBody, TargetWriter wr) {
    //   if (fromArray) {
    //     wr.Write($"{DafnySeqClass}.fromRawArrayRange({TypeDescriptor(source.Type.TypeArgs[0], wr, source.tok)}, ");
    //   }
    //
    //   TrParenExpr(source, wr, inLetExprBody);
    //   if (fromArray) {
    //     wr.Write(", ");
    //     if (lo != null) {
    //       TrExprAsInt(lo, wr, inLetExprBody);
    //     }
    //     else {
    //       wr.Write("0");
    //     }
    //
    //     wr.Write(", ");
    //     if (hi != null) {
    //       TrExprAsInt(hi, wr, inLetExprBody);
    //     }
    //     else {
    //       wr.Write("java.lang.reflect.Array.getLength");
    //       TrParenExpr(source, wr, inLetExprBody);
    //     }
    //
    //     wr.Write(")");
    //   }
    //   else {
    //     if (lo != null && hi != null) {
    //       wr.Write(".subsequence(");
    //       TrExprAsInt(lo, wr, inLetExprBody);
    //       wr.Write(", ");
    //       TrExprAsInt(hi, wr, inLetExprBody);
    //       wr.Write(")");
    //     }
    //     else if (lo != null) {
    //       wr.Write(".drop");
    //       TrParenExpr(lo, wr, inLetExprBody);
    //     }
    //     else if (hi != null) {
    //       wr.Write(".take");
    //       TrParenExpr(hi, wr, inLetExprBody);
    //     }
    //   }
     }

    protected override void EmitIndexCollectionSelect(Expression source, Expression index, bool inLetExprBody,
      TargetWriter wr) {
      // Taken from C# compiler, assuming source is a DafnySequence type.
      TrParenExpr(source, wr, inLetExprBody);
      if (source.Type.AsCollectionType is MultiSetType) {
        TrParenExpr(".multiplicity", index, wr, inLetExprBody);
      }
      else if (source.Type.AsCollectionType is MapType) {
        TrParenExpr(".get", index, wr, inLetExprBody);
      }
      else {
        TrParenExpr(".select", index, wr, inLetExprBody);
      }

    }

    protected override void EmitMultiSetFormingExpr(MultiSetFormingExpr expr, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(expr.E, wr, inLetExprBody);
      wr.Write(".asDafnyMultiset()");
    }

    protected override void EmitIndexCollectionUpdate(Expression source, Expression index, Expression value,
      bool inLetExprBody,
      TargetWriter wr, bool nativeIndex = false) {
      TrParenExpr(source, wr, inLetExprBody);
      wr.Write(".update(");
      TrExpr(index, wr, inLetExprBody);
      wr.Write(", ");
      TrExpr(value, wr, inLetExprBody);
      wr.Write(")");
    }

    protected override void EmitRotate(Expression e0, Expression e1, bool isRotateLeft, TargetWriter wr,
      bool inLetExprBody, FCE_Arg_Translator tr) {
      string nativeName = null, literalSuffix = null;
      bool needsCast = false;
      var nativeType = AsNativeType(e0.Type);
      if (nativeType != null) {
        GetNativeInfo(nativeType.Sel, out nativeName, out literalSuffix, out needsCast);
      }

      var leftShift = nativeType == null ? ".shiftLeft" : "<<";
      var rightShift = nativeType == null ? ".shiftRight" : ">>>";
      // ( e0 op1 e1) | (e0 op2 (width - e1))
      if (needsCast) {
        wr.Write("(" + nativeName + ")(" + CastIfSmallNativeType(e0.Type) + "(");
      }

      wr.Write("(");
      EmitShift(e0, e1, isRotateLeft ? leftShift : rightShift, isRotateLeft, nativeType, true, wr, inLetExprBody, tr);
      wr.Write(")");
      if (nativeType == null) {
        wr.Write(".or");
      }
      else {
        wr.Write("|");
      }

      wr.Write("(");
      EmitShift(e0, e1, isRotateLeft ? rightShift : leftShift, !isRotateLeft, nativeType, false, wr, inLetExprBody, tr);
      wr.Write(")))");
      if (needsCast) {
        wr.Write("))");
      }
    }

    void EmitShift(Expression e0, Expression e1, string op, bool truncate, NativeType /*?*/ nativeType, bool firstOp,
      TargetWriter wr, bool inLetExprBody, FCE_Arg_Translator tr) {
      var bv = e0.Type.AsBitVectorType;
      if (truncate) {
        wr = EmitBitvectorTruncation(bv, true, wr);
      }

      tr(e0, wr, inLetExprBody);
      wr.Write($" {op} ");
      if (!firstOp) {
        wr.Write($"({bv.Width} - ");
      }

      wr.Write("((");
      tr(e1, wr, inLetExprBody);
      wr.Write(")");
      if (AsNativeType(e1.Type) == null) {
        wr.Write(".intValue()");
      }

      if (!firstOp) {
        wr.Write(")");
      }
    }

    protected override TargetWriter EmitBitvectorTruncation(BitvectorType bvType, bool surroundByUnchecked,
      TargetWriter wr) {
      string nativeName = null, literalSuffix = null;
      bool needsCastAfterArithmetic = false;
      if (bvType.NativeType != null) {
        GetNativeInfo(bvType.NativeType.Sel, out nativeName, out literalSuffix, out needsCastAfterArithmetic);
      }

      // --- Before
      if (bvType.NativeType == null) {
        wr.Write("((");
      }
      else {
        wr.Write($"({nativeName}) {CastIfSmallNativeType(bvType)}((");
      }

      // --- Middle
      var middle = wr.Fork();
      // --- After
      // do the truncation, if needed
      if (bvType.NativeType == null) {
        wr.Write($").and((java.math.BigInteger.ONE.shiftLeft({bvType.Width})).subtract(java.math.BigInteger.ONE)))");
      }
      else {
        if (bvType.NativeType.Bitwidth != bvType.Width) {
          // print in hex, because that looks nice
          wr.Write($") & {CastIfSmallNativeType(bvType)}0x{(1UL << bvType.Width) - 1:X}{literalSuffix})");
        }
        else {
          wr.Write("))"); // close the parentheses for the cast
        }
      }

      return middle;
    }

    protected override bool CompareZeroUsingSign(Type type) {
      // Everything is boxed, so everything benefits from avoiding explicit 0
      return true;
    }

    protected override TargetWriter EmitSign(Type type, TargetWriter wr) {
      TargetWriter w;
      var nt = AsNativeType(type);
      if (nt == null) {
        w = wr.Fork();
        wr.Write(".signum()");
      }
      else if (nt.LowerBound >= 0) {
        wr.Write("(");
        w = wr.Fork();
        wr.Write(" == 0 ? 0 : 1)");
      }
      else {
        wr.Write($"{HelperClass(nt)}.signum(");
        w = wr.Fork();
        wr.Write(")");
      }

      return w;
    }

    protected override IClassWriter /*?*/ DeclareDatatype(DatatypeDecl dt, TargetWriter wr) {
      if (dt is TupleTypeDecl) {
        tuples.Add(((TupleTypeDecl) dt).Dims);
        return null;
      }
      else {
        var w = CompileDatatypeBase(dt, wr);
        CompileDatatypeConstructors(dt, wr);
        return w;
      }
    }

    IClassWriter CompileDatatypeBase(DatatypeDecl dt, TargetWriter wr) {
      string DtT = dt.CompileName;
      string DtT_protected = IdProtect(DtT);
      string DtT_TypeArgs = "";
      if (dt.TypeArgs.Count != 0) {
        DtT_TypeArgs = "<" + TypeParameters(dt.TypeArgs) + ">";
        DtT += DtT_TypeArgs;
        DtT_protected += DtT_TypeArgs;
      }

      var filename = $"{ModulePath}/{dt}.java";
      wr = wr.NewFile(filename);
      FileCount += 1;
      wr.WriteLine($"// Class {DtT_protected}");
      wr.WriteLine($"// Dafny class {DtT_protected} compiled into Java");
      wr.WriteLine($"package {ModuleName};");
      wr.WriteLine();
      EmitImports(wr, out _);
      wr.WriteLine();
      // from here on, write everything into the new block created here:
      //TODO: Figure out how to resolve type checking warnings
      EmitSuppression(wr);
      var btw = wr.NewNamedBlock("public{0} class {1}", dt.IsRecordType ? "" : " abstract", DtT_protected);
      wr = btw;
      // constructor
      if (dt.IsRecordType) {
        DatatypeFieldsAndConstructor(dt.Ctors[0], 0, wr);
      }
      else {
        wr.WriteLine($"public {IdName(dt)}() {{ }}");
      }

      var typeArgsStr = Util.Comma(dt.TypeArgs, IdName);
      var usedTypeArgs = UsedTypeParameters(dt);
      var usedTypeArgsStr = Util.Comma(usedTypeArgs, IdName);
      var typeDescArgsStr = Util.Comma(usedTypeArgs, FormatTypeDescriptorVariable);
      TargetWriter wDefault;
      if (dt.TypeArgs.Count == 0) {
        wr.Write($"static {IdName(dt)} theDefault = ");
        wDefault = wr.Fork();
        wr.WriteLine(";");

        using (var w = wr.NewNamedBlock($"public static {IdName(dt)} Default()")) {
          w.WriteLine("return theDefault;");
        }
      }
      else {
        var w = wr.NewBigBlock(
          $"public static <{typeArgsStr}> {dt}<{typeArgsStr}> Default({Util.Comma(usedTypeArgs, tp => $"{TypeClass}<{IdName(tp)}> {FormatTypeDescriptorVariable(tp)}")})",
          "");
        w.Write("return ");
        wDefault = w.Fork();
        w.WriteLine(";");
      }

      DatatypeCtor defaultCtor;
      if (dt is IndDatatypeDecl) {
        defaultCtor = ((IndDatatypeDecl) dt).DefaultCtor;
      }
      else {
        defaultCtor = ((CoDatatypeDecl) dt).Ctors[0];
      }

      string arguments = "";
      string sep = "";
      foreach (Formal f in defaultCtor.Formals) {
        if (!f.IsGhost) {
          arguments += sep + DefaultValue(f.Type, wDefault, f.Tok);
          sep = ", ";
        }
      }

      EmitDatatypeValue(dt, defaultCtor, dt is CoDatatypeDecl, arguments, wDefault);
      EmitTypeMethod(IdName(dt), dt.TypeArgs, usedTypeArgs, $"Default({typeDescArgsStr})", wr);
      // create methods
      // TODO:  Need to revisit this. Java cannot reference generic types in a static context, so this wont work.
      // (Yes, it can: public static <T1, T2> Foo create_Bar(T1 arg1, T2 arg2) { ... })
//      foreach (var ctor in dt.Ctors) {
//        wr.Write("public static {0} {1}(", DtT_protected, DtCreateName(ctor));
//        WriteFormals("", ctor.Formals, wr);
//        var w = wr.NewBlock(")");
//        w.Write("return new {0}(", DtCtorDeclarationName(ctor, dt.TypeArgs));
//        var sep = "";
//        var i = 0;
//        foreach (var arg in ctor.Formals) {
//          if (!arg.IsGhost) {
//            w.Write("{0}{1}", sep, FormalName(arg, i));
//            sep = ", ";
//            i++;
//          }
//        }
//        w.WriteLine(");");
//      }
      // query properties
      foreach (var ctor in dt.Ctors) {
        if (dt.IsRecordType) {
          wr.WriteLine($"public boolean is_{ctor.CompileName}() {{ return true; }}");
        }
        else {
          wr.WriteLine(
            $"public boolean is_{ctor.CompileName}() {{ return this instanceof {dt.CompileName}_{ctor.CompileName}; }}");
        }
      }

      if (dt is CoDatatypeDecl) {
        wr.WriteLine($"public abstract {DtT_protected} Get();");
      }

      if (dt.HasFinitePossibleValues) {
        Contract.Assert(dt.TypeArgs.Count == 0);
        var w = wr.NewNamedBlock($"public static java.util.ArrayList<{DtT_protected}> AllSingletonConstructors()");
        string arraylist = "singleton_iterator";
        w.WriteLine($"java.util.ArrayList<{DtT_protected}> {arraylist} = new java.util.ArrayList<>();");
        foreach (var ctor in dt.Ctors) {
          Contract.Assert(ctor.Formals.Count == 0);
          w.WriteLine("{0}.add(new {1}{2}());", arraylist, DtT_protected,
            dt.IsRecordType ? "" : $"_{ctor.CompileName}");
        }

        w.WriteLine($"return {arraylist};");
      }

      // destructors
      foreach (var ctor in dt.Ctors) {
        foreach (var dtor in ctor.Destructors) {
          if (dtor.EnclosingCtors[0] == ctor) {
            var arg = dtor.CorrespondingFormals[0];
            if (!arg.IsGhost && arg.HasName) {
              using (var wDtor =
                wr.NewNamedBlock($"public {TypeName(arg.Type, wr, arg.tok)} dtor_{arg.CompileName}()")) {
                if (dt.IsRecordType) {
                  wDtor.WriteLine($"return this.{IdName(arg)};");
                }
                else {
                  wDtor.WriteLine("{0} d = this{1};", DtT_protected, dt is CoDatatypeDecl ? ".Get()" : "");
                  var n = dtor.EnclosingCtors.Count;
                  for (int i = 0; i < n - 1; i++) {
                    var ctor_i = dtor.EnclosingCtors[i];
                    Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[i].CompileName);
                    wDtor.WriteLine("if (d instanceof {0}_{1}{2}) {{ return (({0}_{1}{2})d).{3}; }}", dt.CompileName,
                      ctor_i.CompileName, DtT_TypeArgs, IdName(arg));
                  }

                  Contract.Assert(arg.CompileName == dtor.CorrespondingFormals[n - 1].CompileName);
                  wDtor.WriteLine(
                    $"return (({dt.CompileName}_{dtor.EnclosingCtors[n - 1].CompileName}{DtT_TypeArgs})d).{IdName(arg)};");
                }
              }
            }
          }
        }
      }

      // FIXME: This is dodgy.  We can set the constructor body writer to null
      // only because we don't expect to use it, which is only because we don't
      // expect there to be fields.
      //return new ClassWriter(this, btw, ctorBodyWriter: null);
      return null;
    }

    void CompileDatatypeConstructors(DatatypeDecl dt, TargetWriter wrx) {
      Contract.Requires(dt != null);
      string typeParams = dt.TypeArgs.Count == 0 ? "" : $"<{TypeParameters(dt.TypeArgs)}>";
      if (dt.IsRecordType) {
        // There is only one constructor, and it is populated by CompileDatatypeBase
        return;
      }

      int constructorIndex = 0; // used to give each constructor a different name
      foreach (DatatypeCtor ctor in dt.Ctors) {
        var filename = $"{ModulePath}/{DtCtorDeclarationName(ctor)}.java";
        var wr = wrx.NewFile(filename);
        FileCount += 1;
        wr.WriteLine($"// Class {DtCtorDeclarationName(ctor, dt.TypeArgs)}");
        wr.WriteLine($"// Dafny class {DtCtorDeclarationName(ctor, dt.TypeArgs)} compiled into Java");
        wr.WriteLine($"package {ModuleName};");
        wr.WriteLine();
        EmitImports(wr, out _);
        wr.WriteLine();
        EmitSuppression(wr);
        var w = wr.NewNamedBlock(
          $"public class {DtCtorDeclarationName(ctor, dt.TypeArgs)} extends {IdName(dt)}{typeParams}");
        DatatypeFieldsAndConstructor(ctor, constructorIndex, w);
        constructorIndex++;
      }

      if (dt is CoDatatypeDecl) {
        var filename = $"{ModulePath}/{dt.CompileName}__Lazy.java";
        var wr = wrx.NewFile(filename);
        FileCount += 1;
        wr.WriteLine($"// Class {dt.CompileName}__Lazy");
        wr.WriteLine($"// Dafny class {dt.CompileName}__Lazy compiled into Java");
        wr.WriteLine($"package {ModuleName};");
        wr.WriteLine();
        EmitImports(wr, out _);
        wr.WriteLine();
        EmitSuppression(wr); //TODO: Fix implementations so they do not need this suppression
        var w = wr.NewNamedBlock($"public class {dt.CompileName}__Lazy{typeParams} extends {IdName(dt)}{typeParams}");
        w.WriteLine($"interface Computer {{ {dt.CompileName} run(); }}");
        w.WriteLine("Computer c;");
        w.WriteLine($"{dt.CompileName}{typeParams} d;");
        w.WriteLine($"public {dt.CompileName}__Lazy(Computer c) {{ this.c = c; }}");
        w.WriteLine(
          $"public {dt.CompileName}{typeParams} Get() {{ if (c != null) {{ d = c.run(); c = null; }} return d; }}");
        w.WriteLine("public String toString() { return Get().toString(); }");
      }
    }

    void DatatypeFieldsAndConstructor(DatatypeCtor ctor, int constructorIndex, TargetWriter wr) {
      Contract.Requires(ctor != null);
      Contract.Requires(0 <= constructorIndex && constructorIndex < ctor.EnclosingDatatype.Ctors.Count);
      Contract.Requires(wr != null);
      var dt = ctor.EnclosingDatatype;
      var i = 0;
      foreach (Formal arg in ctor.Formals) {
        if (!arg.IsGhost) {
          wr.WriteLine($"public {TypeName(arg.Type, wr, arg.tok)} {FormalName(arg, i)};");
          i++;
        }
      }

      wr.Write($"public {DtCtorDeclarationName(ctor)}(");
      WriteFormals("", ctor.Formals, wr);
      using (var w = wr.NewBlock(")")) {
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            w.WriteLine($"this.{FormalName(arg, i)} = {FormalName(arg, i)};");
            i++;
          }
        }
      }

      if (ctor.Formals.Count > 0) {
        wr.Write($"public {DtCtorDeclarationName(ctor)}(){{}}");
      }

      if (dt is CoDatatypeDecl) {
        string typeParams = dt.TypeArgs.Count == 0 ? "" : $"<{TypeParameters(dt.TypeArgs)}>";
        wr.WriteLine($"public {dt.CompileName}{typeParams} Get() {{ return this; }}");
      }

      // Equals method
      using (var w = wr.NewBlock("\n@Override\npublic boolean equals(Object other)")) {
        w.WriteLine("if (this == other) return true;");
        w.WriteLine("if (other == null) return false;");
        w.WriteLine("if (getClass() != other.getClass()) return false;");
        if (ctor.Formals.Count > 0) {
          string typeParams = dt.TypeArgs.Count == 0 ? "" : $"<{TypeParameters(dt.TypeArgs)}>";
          w.WriteLine("{0} o = ({0})other;", DtCtorDeclarationName(ctor, dt.TypeArgs));
          w.Write("return ");
          i = 0;
          foreach (Formal arg in ctor.Formals) {
            if (!arg.IsGhost) {
              string nm = FormalName(arg, i);
              if (i != 0)
                w.Write(" && ");
              if (IsDirectlyComparable(arg.Type)) {
                w.Write($"this.{nm} == o.{nm}");
              }
              else {
                w.Write($"{nm}.equals(o.{nm})");
              }

              i++;
            }
          }

          w.WriteLine(";");
        }
        else {
          w.WriteLine("return true;");
        }
      }

      // GetHashCode method (Uses the djb2 algorithm)
      using (var w = wr.NewBlock("\n@Override\npublic int hashCode()")) {
        w.WriteLine("long hash = 5381;");
        w.WriteLine($"hash = ((hash << 5) + hash) + {constructorIndex};");
        i = 0;
        foreach (Formal arg in ctor.Formals) {
          if (!arg.IsGhost) {
            string nm = FormalName(arg, i);
            w.Write("hash = ((hash << 5) + hash) + ");
            if (IsJavaPrimitiveType(arg.Type)) {
              w.WriteLine($"{BoxedTypeName(arg.Type, w, Bpl.Token.NoToken)}.hashCode(this.{nm});");
            }
            else {
              w.WriteLine($"this.{nm}.hashCode();");
            }

            i++;
          }
        }

        w.WriteLine("return (int) hash;");
      }

      using (var w = wr.NewBlock("\n@Override\npublic String toString()")) {
        string nm;
        if (dt is TupleTypeDecl) {
          nm = "";
        }
        else {
          nm = (dt.Module.IsDefaultModule ? "" : dt.Module.Name + ".") + dt.Name + "." + ctor.Name;
        }

        if (dt is TupleTypeDecl && ctor.Formals.Count == 0) {
          // here we want parentheses and no name
          w.WriteLine("return \"()\";");
        }
        else if (dt is CoDatatypeDecl) {
          w.WriteLine($"return \"{nm}\";");
        }
        else {
          var tempVar = GenVarName("s", ctor.Formals);
          w.WriteLine($"StringBuilder {tempVar} = new StringBuilder();");
          w.WriteLine($"{tempVar}.append(\"{nm}\");");
          if (ctor.Formals.Count != 0) {
            w.WriteLine($"{tempVar}.append(\"(\");");
            i = 0;
            foreach (var arg in ctor.Formals) {
              if (!arg.IsGhost) {
                if (i != 0) {
                  w.WriteLine($"{tempVar}.append(\", \");");
                }

                w.Write($"{tempVar}.append(");
                var memberName = FormalName(arg, i);
                if (IsJavaPrimitiveType(arg.Type)) {
                  w.Write($"this.{memberName}");
                }
                else {
                  w.Write($"this.{memberName} == null ? \"\" : this.{memberName}");
                }

                w.WriteLine(");");
                i++;
              }
            }

            w.WriteLine($"{tempVar}.append(\")\");");
          }

          w.WriteLine($"return {tempVar}.toString();");
        }
      }
    }

    string DtCtorDeclarationName(DatatypeCtor ctor, List<TypeParameter> typeParams) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var s = DtCtorDeclarationName(ctor);
      if (typeParams != null && typeParams.Count != 0) {
        s += "<" + TypeParameters(typeParams) + ">";
      }

      return s;
    }

    string DtCtorDeclarationName(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var dt = ctor.EnclosingDatatype;
      return dt.IsRecordType ? IdName(dt) : dt.CompileName + "_" + ctor.CompileName;
    }

    string DtCtorName(DatatypeCtor ctor, List<Type> typeArgs, TextWriter wr) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var s = DtCtorName(ctor);
      if (typeArgs != null && typeArgs.Count != 0) {
        s += "<" + BoxedTypeNames(typeArgs, wr, ctor.tok) + ">";
      }

      return s;
    }

    string DtCtorName(DatatypeCtor ctor) {
      Contract.Requires(ctor != null);
      Contract.Ensures(Contract.Result<string>() != null);

      var dt = ctor.EnclosingDatatype;
      if (dt is TupleTypeDecl tupleDecl) {
        return DafnyTupleClass(tupleDecl.TypeArgs.Count);
      }

      var dtName = IdProtect(dt.CompileName);
      return dt.IsRecordType ? dtName : dtName + "_" + ctor.CompileName;
    }

    string DtCreateName(DatatypeCtor ctor) {
      if (ctor.EnclosingDatatype.IsRecordType) {
        return "create";
      }

      return "create_" + ctor.CompileName;
    }

    protected override void EmitPrintStmt(TargetWriter wr, Expression arg) {
      wr.Write("System.out.print(");
      EmitToString(wr, arg);
      wr.WriteLine(");");
    }

    protected void EmitToString(TargetWriter wr, Expression arg) {
      if (arg.Type.IsArrowType) {
        wr.Write(IdName(((IdentifierExpr) ((ConcreteSyntaxExpression) arg).ResolvedExpression).Var) +
                 " == null ? null : \"Function\"");
      }
      else if (AsNativeType(arg.Type) != null && AsNativeType(arg.Type).LowerBound >= 0) {
        var nativeName = GetNativeTypeName(AsNativeType(arg.Type));
        switch (AsNativeType(arg.Type).Sel) {
          case NativeType.Selection.Byte:
            wr.Write("Integer.toUnsignedString(Byte.toUnsignedInt(");
            TrExpr(arg, wr, false);
            wr.Write("))");
            break;
          case NativeType.Selection.UShort:
            wr.Write("Integer.toUnsignedString(Short.toUnsignedInt(");
            TrExpr(arg, wr, false);
            wr.Write("))");
            break;
          case NativeType.Selection.UInt:
            wr.Write("Integer.toUnsignedString(");
            TrExpr(arg, wr, false);
            wr.Write(")");
            break;
          case NativeType.Selection.ULong:
            wr.Write("Long.toUnsignedString(");
            TrExpr(arg, wr, false);
            wr.Write(")");
            break;
          default:
            // Should be an unsigned type by assumption
            Contract.Assert(false);
            throw new cce.UnreachableException();
        }
      }
      else {
        // TODO-RS: This doesn't handle strings printed out as part of datatypes
        bool isString = arg.Type.AsCollectionType != null &&
                        arg.Type.AsCollectionType.AsSeqType != null &&
                        arg.Type.AsCollectionType.AsSeqType.Arg is CharType;
        if (!isString) {
          wr.Write("String.valueOf(");
        }

        TrExpr(arg, wr, false);
        if (isString) {
          wr.Write(".verbatimString()");
        }
        else {
          wr.Write(")");
        }
      }
    }

    protected override string IdProtect(string name) {
      return PublicIdProtect(name);
    }

    public static string PublicIdProtect(string name) {
      name = name.Replace("_module", "_System");
      if (name == "" || name.First() == '_') {
        return name; // no need to further protect this name
      }

      // TODO: Finish with all the public IDs that need to be protected
      switch (name) {
        // keywords Java 8 and before
        // https://docs.oracle.com/javase/tutorial/java/nutsandbolts/_keywords.html
        case "abstract":
        case "assert":
        case "break":
        case "byte":
        case "case":
        case "catch":
        case "char":
        case "class":
        case "continue":
        case "default":
        case "do":
        case "double":
        case "else":
        case "enum":
        case "extends":
        case "final":
        case "finally":
        case "float":
        case "for":
        case "if":
        case "implements":
        case "import":
        case "instanceof":
        case "int":
        case "interface":
        case "long":
        case "native":
        case "new":
        case "package":
        case "private":
        case "protected":
        case "public":
        case "return":
        case "short":
        case "static":
        case "strictfp":
        case "super":
        case "switch":
        case "synchronized":
        case "this":
        case "throw":
        case "throws":
        case "transient":
        case "try":
        case "void":
        case "volatile":
        case "while":
        // keywords since Java 9
        case "exports":
        case "module":
        case "requires":
        // no longer used in Java but still reserved as keywords
        case "const":
        case "goto":
        // special identifiers since Java 10
        case "var":
        // literal values
        case "false":
        case "null":
        case "true":
          return name + "_"; // TODO: figure out what to do here (C# uses @, Go uses _, JS uses _$$_)
        default:
          return name; // Package name is not a keyword, so it can be used
      }
    }

    public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText,
      string /*?*/ callToMain, string /*?*/ targetFilename,
      ReadOnlyCollection<string> otherFileNames, bool hasMain, bool runAfterCompile, TextWriter outputWriter,
      out object compilationResult) {
      compilationResult = null;
      foreach (var otherFileName in otherFileNames) {
        if (Path.GetExtension(otherFileName) != ".java") {
          outputWriter.WriteLine($"Unrecognized file as extra input for Java compilation: {otherFileName}");
          return false;
        }

        if (!CopyExternLibraryIntoPlace(mainProgram: targetFilename, externFilename: otherFileName,
          outputWriter: outputWriter)) {
          return false;
        }
      }

      var files = new List<string>();
      foreach (string file in Directory.EnumerateFiles(Path.GetDirectoryName(targetFilename), "*.java",
        SearchOption.AllDirectories)) {
        files.Add($"\"{Path.GetFullPath(file)}\"");
      }

      var classpath = GetClassPath(targetFilename);
      var psi = new ProcessStartInfo("javac", string.Join(" ", files)) {
        CreateNoWindow = true,
        UseShellExecute = false,
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        WorkingDirectory = Path.GetFullPath(Path.GetDirectoryName(targetFilename))
      };
      psi.EnvironmentVariables["CLASSPATH"] = classpath;
      var proc = Process.Start(psi);
      while (!proc.StandardOutput.EndOfStream) {
        outputWriter.WriteLine(proc.StandardOutput.ReadLine());
      }

      while (!proc.StandardError.EndOfStream) {
        outputWriter.WriteLine(proc.StandardError.ReadLine());
      }

      proc.WaitForExit();
      if (proc.ExitCode != 0) {
        throw new Exception($"Error while compiling Java files. Process exited with exit code {proc.ExitCode}");
      }

      return true;
    }

    public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
      string /*?*/ targetFilename,
      ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter) {
      var psi = new ProcessStartInfo("java", Path.GetFileNameWithoutExtension(targetFilename)) {
        CreateNoWindow = true,
        UseShellExecute = false,
        RedirectStandardOutput = true,
        RedirectStandardError = true,
        WorkingDirectory = Path.GetFullPath(Path.GetDirectoryName(targetFilename))
      };
      psi.EnvironmentVariables["CLASSPATH"] = GetClassPath(targetFilename);
      var proc = Process.Start(psi);
      while (!proc.StandardOutput.EndOfStream) {
        outputWriter.WriteLine(proc.StandardOutput.ReadLine());
      }

      while (!proc.StandardError.EndOfStream) {
        outputWriter.WriteLine(proc.StandardError.ReadLine());
      }

      proc.WaitForExit();
      if (proc.ExitCode != 0) {
        throw new Exception(
          $"Error while running Java file {targetFilename}. Process exited with exit code {proc.ExitCode}");
      }

      return true;
    }

    protected string GetClassPath(string targetFilename) {
      var assemblyLocation = Assembly.GetExecutingAssembly().Location;
      Contract.Assert(assemblyLocation != null);
      var codebase = Path.GetDirectoryName(assemblyLocation);
      Contract.Assert(codebase != null);
      // DafnyRuntime-1.jar has already been created using Maven. It is added to the java CLASSPATH below.
      return "." + Path.PathSeparator + Path.GetFullPath(Path.GetDirectoryName(targetFilename)) + Path.PathSeparator +
             Path.Combine(codebase, "DafnyRuntime-1.jar");
    }

    static bool CopyExternLibraryIntoPlace(string externFilename, string mainProgram, TextWriter outputWriter) {
      // Grossly, we need to look in the file to figure out where to put it
      var pkgName = FindPackageName(externFilename);
      if (pkgName == null) {
        outputWriter.WriteLine($"Unable to determine package name: {externFilename}");
        return false;
      }

      string baseName = Path.GetFileNameWithoutExtension(externFilename);
      var mainDir = Path.GetDirectoryName(mainProgram);
      Contract.Assert(mainDir != null);
      var tgtDir = Path.Combine(mainDir, pkgName);
      var tgtFilename = Path.Combine(tgtDir, baseName + ".java");
      Directory.CreateDirectory(tgtDir);
      FileInfo file = new FileInfo(externFilename);
      file.CopyTo(tgtFilename, true);
      if (DafnyOptions.O.CompileVerbose) {
        outputWriter.WriteLine($"Additional input {externFilename} copied to {tgtFilename}");
      }

      return true;
    }

    private static string FindPackageName(string externFilename) {
      using (var rd = new StreamReader(new FileStream(externFilename, FileMode.Open, FileAccess.Read))) {
        while (rd.ReadLine() is string line) {
          var match = PackageLine.Match(line);
          if (match.Success) {
            return match.Groups[1].Value;
          }
        }

        return null;
      }
    }

    protected override void EmitReturn(List<Formal> outParams, TargetWriter wr) {
      outParams = outParams.Where(f => !f.IsGhost).ToList();
      if (outParams.Count == 0) {
        wr.WriteLine("return;");
      }
      else if (outParams.Count == 1) {
        wr.WriteLine($"return {IdName(outParams[0])};");
      }
      else {
        tuples.Add(outParams.Count);
        wr.WriteLine($"return new {DafnyTupleClass(outParams.Count)}<>({Util.Comma(outParams, IdName)});");
      }
    }

    private static readonly Regex PackageLine = new Regex(@"^\s*package\s+([a-zA-Z0-9_]+)\s*;$");

    // TODO: See if more types need to be added
    bool IsDirectlyComparable(Type t) {
      Contract.Requires(t != null);
      return t.IsBoolType || t.IsCharType || t.IsRefType || AsJavaNativeType(t) != null;
    }

    protected override void EmitActualTypeArgs(List<Type> typeArgs, Bpl.IToken tok, TextWriter wr) {
      // Todo: see if there is ever a time in java where this is necessary
//      if (typeArgs.Count != 0) {
//        wr.Write("<" + TypeNames(typeArgs, wr, tok) + ">");
//      }
    }

    protected override string GenerateLhsDecl(string target, Type type, TextWriter wr, Bpl.IToken tok) {
      return TypeName(type, wr, tok) + " " + target;
    }

    protected override void EmitNew(Type type, Bpl.IToken tok, CallStmt initCall, TargetWriter wr) {
      var ctor = (Constructor) initCall?.Method; // correctness of cast follows from precondition of "EmitNew"
      wr.Write($"new {TypeName(type, wr, tok)}(");
      if (type is UserDefinedType definedType) {
        EmitRuntimeTypeDescriptors(definedType.ResolvedClass.TypeArgs, definedType.TypeArgs, useAll: false, tok, wr);
      }

      if (ctor != null && ctor.IsExtern(out _, out _)) {
        // the arguments of any external constructor are placed here
        string sep = "";
        for (int i = 0; i < ctor.Ins.Count; i++) {
          Formal p = ctor.Ins[i];
          if (!p.IsGhost) {
            wr.Write(sep);
            TrExpr(initCall.Args[i], wr, false);
            sep = ", ";
          }
        }
      }

      wr.Write(")");
    }


    private void EmitRuntimeTypeDescriptors(List<TypeParameter> typeParams, List<Type> typeArgs, bool useAll,
      Bpl.IToken tok, TargetWriter wr) {
      Contract.Assert(typeParams.Count == typeArgs.Count);

      var sep = "";
      for (var i = 0; i < typeParams.Count; i++) {
        var tp = typeParams[i];
        var actual = typeArgs[i];

        if (useAll || tp.Characteristics.MustSupportZeroInitialization) {
          wr.Write(sep);
          wr.Write(TypeDescriptor(actual, wr, tok));
          sep = ", ";
        }
      }
    }

    private string TypeDescriptor(Type type, TextWriter wr, Bpl.IToken tok) {
      type = type.NormalizeExpand();
      if (type is BoolType) {
        return $"{TypeClass}.BOOLEAN";
      }
      else if (type is CharType) {
        return $"{TypeClass}.CHAR";
      }
      else if (type is IntType || type is BigOrdinalType) {
        return $"{TypeClass}.BIG_INTEGER";
      }
      else if (type is RealType) {
        return $"{TypeClass}.BIG_RATIONAL";
      }
      else if (AsNativeType(type) != null) {
        return GetNativeTypeDescriptor(AsNativeType(type));
      }
      else if (type is BitvectorType bvt) {
        // already checked if it has a native type
        return $"{TypeClass}.BIG_INTEGER";
      }
      else if (type.AsNewtype != null) {
        // already checked if it has a native type
        return TypeDescriptor(type.AsNewtype.BaseType, wr, tok);
      }
      else if (type.IsObjectQ) {
        return $"{TypeClass}.OBJECT";
      }
      else if (type.IsArrayType) {
        ArrayClassDecl at = type.AsArrayType;
        var elType = UserDefinedType.ArrayElementType(type);
        var elTypeName = TypeName(elType, wr, tok);
        if (at.Dims > 1) {
          arrays.Add(at.Dims);
          return $"{DafnyMultiArrayClass(at.Dims)}.<{elTypeName}>{TypeMethodName}()";
        }
        else if (elType is BoolType) {
          return $"{TypeClass}.BOOLEAN_ARRAY";
        }
        else if (elType is CharType) {
          return $"{TypeClass}.CHAR_ARRAY";
        }
        else if (AsNativeType(type) != null) {
          switch (AsJavaNativeType(type)) {
            case JavaNativeType.Byte: return $"{TypeClass}.BYTE_ARRAY";
            case JavaNativeType.Short: return $"{TypeClass}.SHORT_ARRAY";
            case JavaNativeType.Int: return $"{TypeClass}.INT_ARRAY";
            case JavaNativeType.Long: return $"{TypeClass}.LONG_ARRAY";
            default:
              Contract.Assert(false);
              throw new cce.UnreachableException();
          }
        }
        else {
          return $"({TypeDescriptor(elType, wr, tok)}).arrayType()";
        }
      }
      else if (type.IsTypeParameter) {
        return FormatTypeDescriptorVariable(type.AsTypeParameter.CompileName);
      }
      else if (type is ArrowType arrowType && arrowType.Arity == 1) {
        // Can't go the usual route because java.util.function.Function doesn't have a _type() method
        return
          $"{TypeClass}.function({TypeDescriptor(arrowType.Args[0], wr, tok)}, {TypeDescriptor(arrowType.Result, wr, tok)})";
      }
      else if (type is UserDefinedType udt) {
        var s = FullTypeName(udt);
        var cl = udt.ResolvedClass;
        Contract.Assert(cl != null);
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return $"{TypeClass}.LONG";
        }
        else if (cl is TupleTypeDecl tupleDecl) {
          s = $"{DafnyTupleClass(tupleDecl.TypeArgs.Count)}";
        }
        else if (DafnyOptions.O.IronDafny &&
                 !(type is ArrowType) &&
                 cl != null &&
                 cl.Module != null &&
                 !cl.Module.IsDefaultModule) {
          s = cl.FullCompileName;
        }

        if (cl.IsExtern(out _, out _)) {
          var td = $"{TypeClass}.<{TypeName(type, wr, tok)}> findType({s}.class";
          if (udt.TypeArgs != null && udt.TypeArgs.Count > 0) {
            td += $", {Util.Comma(udt.TypeArgs, arg => TypeDescriptor(arg, wr, tok))}";
          }

          return td + ")";
        }

        List<Type> relevantTypeArgs;
        if (type is ArrowType) {
          relevantTypeArgs = type.TypeArgs;
        }
        else if (cl is TupleTypeDecl) {
          relevantTypeArgs = new List<Type>();
        }
        else if (cl is DatatypeDecl dt) {
          UsedTypeParameters(dt, udt.TypeArgs, out _, out relevantTypeArgs);
        }
        else {
          relevantTypeArgs = new List<Type>();
          for (int i = 0; i < cl.TypeArgs.Count; i++) {
            if (cl.TypeArgs[i].Characteristics.MustSupportZeroInitialization) {
              relevantTypeArgs.Add(udt.TypeArgs[i]);
            }
          }
        }

        return AddTypeDescriptorArgs(s, udt.TypeArgs, relevantTypeArgs, wr, udt.tok);
      }
      else if (type is SetType setType) {
        return AddTypeDescriptorArgs(DafnySetClass, setType.TypeArgs, setType.TypeArgs, wr, tok);
      }
      else if (type is SeqType seqType) {
        return AddTypeDescriptorArgs(DafnySeqClass, seqType.TypeArgs, seqType.TypeArgs, wr, tok);
      }
      else if (type is MultiSetType multiSetType) {
        return AddTypeDescriptorArgs(DafnyMultiSetClass, multiSetType.TypeArgs, multiSetType.TypeArgs, wr, tok);
      }
      else if (type is MapType mapType) {
        return AddTypeDescriptorArgs(DafnyMapClass, mapType.TypeArgs, mapType.TypeArgs, wr, tok);
      }
      else {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    }

    private string GetNativeTypeDescriptor(NativeType nt) {
      switch (AsJavaNativeType(nt)) {
        case JavaNativeType.Byte: return $"{TypeClass}.BYTE";
        case JavaNativeType.Short: return $"{TypeClass}.SHORT";
        case JavaNativeType.Int: return $"{TypeClass}.INT";
        case JavaNativeType.Long: return $"{TypeClass}.LONG";
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();
      }
    }

    private string AddTypeDescriptorArgs(string fullCompileName, List<Type> typeArgs, List<Type> relevantTypeArgs,
      TextWriter wr, Bpl.IToken tok) {
      string s = $"{IdProtect(fullCompileName)}.";
      if (typeArgs != null && typeArgs.Count != 0) {
        s += $"<{BoxedTypeNames(typeArgs, wr, tok)}>";
      }

      s += $"{TypeMethodName}(";
      s += Util.Comma(relevantTypeArgs, arg => TypeDescriptor(arg, wr, tok));
      return s + ")";
    }

    int WriteRuntimeTypeDescriptorsFormals(List<TypeParameter> typeParams, bool useAllTypeArgs, TargetWriter wr,
      string prefix = "") {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      int c = 0;
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || tp.Characteristics.MustSupportZeroInitialization) {
          wr.Write($"{prefix}{TypeClass}<{tp.Name}> {FormatTypeDescriptorVariable(tp.Name)}");
          prefix = ", ";
          c++;
        }
      }

      return c;
    }

    int WriteRuntimeTypeDescriptorsFormals(Method m, List<TypeParameter> typeParams, bool useAllTypeArgs,
      TargetWriter wr, string prefix = "") {
      Contract.Requires(typeParams != null);
      Contract.Requires(wr != null);

      int c = 0;
      foreach (var tp in typeParams) {
        if (useAllTypeArgs || tp.Characteristics.MustSupportZeroInitialization || OutContainsParam(m.Outs, tp)) {
          wr.Write($"{prefix}{TypeClass}<{tp.CompileName}> {FormatTypeDescriptorVariable(tp)}");
          prefix = ", ";
          c++;
        }
      }

      return c;
    }

    bool OutContainsParam(List<Formal> l, TypeParameter tp) {
      foreach (Formal f in l) {
        if (f.Type.IsTypeParameter && f.Type.AsTypeParameter.Equals(tp) || f.Type.AsCollectionType != null &&
            f.Type.AsCollectionType.Arg.IsTypeParameter && f.Type.AsCollectionType.Arg.AsTypeParameter.Equals(tp)) {
          return true;
        }
      }

      return false;
    }

    protected override void EmitSetComprehension(TargetWriter wr, Expression expr, String collection_name) {
      var e = (SetComprehension) expr;
      wr.Write($"java.util.ArrayList<{BoxedTypeName(((SetType) expr.Type).Arg, wr, null)}> {collection_name} = ");
      EmitCollectionBuilder_New(e.Type.AsSetType, e.tok, wr);
      wr.WriteLine(";");
    }

    protected override void OrganizeModules(Program program, out List<ModuleDefinition> modules) {
      modules = new List<ModuleDefinition>();
      foreach (var m in program.CompileModules) {
        if (!m.IsDefaultModule && !m.Name.Equals("_System")) {
          modules.Add(m);
        }
      }

      foreach (var m in program.CompileModules) {
        if (m.Name.Equals("_System")) {
          modules.Add(m);
        }
      }

      foreach (var m in program.CompileModules) {
        if (m.IsDefaultModule) {
          modules.Add(m);
        }
      }
    }

    protected override void EmitAssignment(out TargetWriter wLhs, Type /*?*/ lhsType, out TargetWriter wRhs,
      Type /*?*/ rhsType, TargetWriter wr) {
      wLhs = wr.Fork();
      wr.Write(" = ");
      TargetWriter w;
      w = rhsType != null ? EmitCoercionIfNecessary(@from: rhsType, to: lhsType, tok: Bpl.Token.NoToken, wr: wr) : wr;
      wRhs = w.Fork();
      EndStmt(wr);
    }

    protected override void EmitDatatypeValue(DatatypeValue dtv, string arguments, TargetWriter wr) {
      var dt = dtv.Ctor.EnclosingDatatype;
      EmitDatatypeValue(dt, dtv.Ctor, dtv.IsCoCall, arguments, wr);
    }

    void EmitDatatypeValue(DatatypeDecl dt, DatatypeCtor ctor, bool isCoCall, string arguments, TargetWriter wr) {
      var dtName = dt is TupleTypeDecl tupleDecl ? DafnyTupleClass(tupleDecl.TypeArgs.Count) : dt.CompileName;
      var ctorName = ctor.CompileName;
      var typeParams = dt.TypeArgs.Count == 0 ? "" : "<>";
      //TODO: Determine if this implementation is ever needed
//      var typeDecl = dtv.InferredTypeArgs.Count == 0
//        ? ""
//        : string.Format("new {0}", TypeNames(dtv.InferredTypeArgs, wr, dtv.tok));
      if (!isCoCall) {
        wr.Write("new {0}{1}{2}", dtName, dt.IsRecordType ? "" : "_" + ctorName, typeParams);
        // For an ordinary constructor (that is, one that does not guard any co-recursive calls), generate:
        //   new Dt_Cons<T>( args )
        if (arguments != null && !arguments.Equals("")) {
          wr.Write($"({arguments})");
        }
        else {
          wr.Write("()");
        }
      }
      else {
        wr.Write($"new {dt.CompileName}__Lazy(");
        wr.Write("() -> { return ");
        wr.Write($"new {DtCtorName(ctor)}({arguments})");
        wr.Write("; })");
      }
    }

    protected override BlockTargetWriter CreateLambda(List<Type> inTypes, Bpl.IToken tok, List<string> inNames,
      Type resultType, TargetWriter wr, bool untyped = false) {
      if (inTypes.Count != 1) {
        functions.Add(inTypes.Count);
      }

      wr.Write('(');
      if (!untyped) {
        wr.Write("({0}<{1}{2}>)", DafnyFunctionIface(inTypes.Count),
          Util.Comma("", inTypes, t => BoxedTypeName(t, wr, tok) + ", "), BoxedTypeName(resultType, wr, tok));
      }

      wr.Write($"({Util.Comma(inNames, nm => nm)}) ->");
      var w = wr.NewExprBlock("");
      wr.Write(")");
      return w;
    }

    protected override BlockTargetWriter CreateIIFE0(Type resultType, Bpl.IToken resultTok, TargetWriter wr) {
      functions.Add(0);
      wr.Write($"(({DafnyFunctionIface(0)}<{BoxedTypeName(resultType, wr, resultTok)}>)(() ->");
      var w = wr.NewBigExprBlock("", ")).apply()");
      return w;
    }

    protected override void EmitUnaryExpr(ResolvedUnaryOp op, Expression expr, bool inLetExprBody, TargetWriter wr) {
      switch (op) {
        case ResolvedUnaryOp.BoolNot:
          TrParenExpr("!", expr, wr, inLetExprBody);
          break;
        case ResolvedUnaryOp.BitwiseNot:
          if (AsNativeType(expr.Type) != null) {
            TrParenExpr(CastIfSmallNativeType(expr.Type) + "~", expr, wr, inLetExprBody);
          }
          else {
            TrParenExpr("", expr, wr, inLetExprBody);
            wr.Write(".not()");
          }

          break;
        case ResolvedUnaryOp.Fresh:
          TrParenExpr("fresh", expr, wr, inLetExprBody);
          break;
        case ResolvedUnaryOp.Cardinality:
          if (expr.Type.AsCollectionType is MultiSetType) {
            TrParenExpr("", expr, wr, inLetExprBody);
            wr.Write(".cardinality()");
          }
          else if (expr.Type.AsCollectionType is SetType || expr.Type.AsCollectionType is MapType) {
            TrParenExpr("java.math.BigInteger.valueOf(", expr, wr, inLetExprBody);
            wr.Write(".size())");
          }
          else if (expr.Type.IsArrayType) {
            TrParenExpr("java.math.BigInteger.valueOf(java.lang.reflect.Array.getLength", expr, wr, inLetExprBody);
            wr.Write(")");
          }
          else {
            TrParenExpr("java.math.BigInteger.valueOf(", expr, wr, inLetExprBody);
            wr.Write(".length())");
          }

          break;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException(); // unexpected unary expression
      }
    }

    // Find the class with static methods like "divideUnsigned" for the type
    private string HelperClass(NativeType nt) {
      return AsJavaNativeType(nt) == JavaNativeType.Long ? "Long" : "Integer";
    }

    protected override void CompileBinOp(BinaryExpr.ResolvedOpcode op, Expression e0, Expression e1, Bpl.IToken tok,
      Type resultType, out string opString,
      out string preOpString, out string postOpString, out string callString, out string staticCallString,
      out bool reverseArguments, out bool truncateResult, out bool convertE1_to_int, TextWriter errorWr) {
      opString = null;
      preOpString = "";
      postOpString = "";
      callString = null;
      staticCallString = null;
      reverseArguments = false;
      truncateResult = false;
      convertE1_to_int = false;

      void doPossiblyNativeBinOp(string o, string name, out string preOpS, out string opS,
        out string postOpS, out string callS) {
        if (AsNativeType(resultType) != null) {
          var nativeName = GetNativeTypeName(AsNativeType(resultType));
          preOpS = $"({nativeName}) {CastIfSmallNativeType(resultType)} (";
          opS = o;
          postOpS = ")";
          callS = null;
        }
        else {
          callS = name;
          preOpS = "";
          opS = null;
          postOpS = "";
        }
      }

      switch (op) {
        case BinaryExpr.ResolvedOpcode.Iff:
          opString = "==";
          break;
        case BinaryExpr.ResolvedOpcode.Imp:
          preOpString = "!";
          opString = "||";
          break;
        case BinaryExpr.ResolvedOpcode.Or:
          opString = "||";
          break;
        case BinaryExpr.ResolvedOpcode.And:
          opString = "&&";
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseAnd:
          doPossiblyNativeBinOp("&", "and", out preOpString, out opString, out postOpString, out callString);
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
          doPossiblyNativeBinOp("|", "or", out preOpString, out opString, out postOpString, out callString);
          break;
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
          doPossiblyNativeBinOp("^", "xor", out preOpString, out opString, out postOpString, out callString);
          break;
        case BinaryExpr.ResolvedOpcode.EqCommon: {
          if (IsHandleComparison(tok, e0, e1, errorWr)) {
            opString = "==";
          }
          else if (e0.Type.IsRefType) {
            opString = "== (Object) ";
          }
          else if (IsDirectlyComparable(e0.Type)) {
            opString = "==";
          }
          else {
            callString = "equals";
          }

          break;
        }
        case BinaryExpr.ResolvedOpcode.NeqCommon: {
          if (IsHandleComparison(tok, e0, e1, errorWr)) {
            opString = "!=";
          }
          else if (e0.Type.IsRefType) {
            opString = "!= (Object) ";
          }
          else if (IsDirectlyComparable(e0.Type)) {
            opString = "!=";
          }
          else {
            preOpString = "!";
            callString = "equals";
          }

          break;
        }
        case BinaryExpr.ResolvedOpcode.Lt:
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.Gt:
          var call = false;
          var argNative = AsNativeType(e0.Type);
          if (argNative != null && argNative.LowerBound >= 0) {
            staticCallString = HelperClass(argNative) + ".compareUnsigned";
            call = true;
          }
          else if (argNative == null) {
            callString = "compareTo";
            call = true;
          }

          if (call) {
            switch (op) {
              case BinaryExpr.ResolvedOpcode.Lt:
                postOpString = " < 0";
                break;
              case BinaryExpr.ResolvedOpcode.Le:
                postOpString = " <= 0";
                break;
              case BinaryExpr.ResolvedOpcode.Ge:
                postOpString = " >= 0";
                break;
              case BinaryExpr.ResolvedOpcode.Gt:
                postOpString = " > 0";
                break;
              default:
                Contract.Assert(false);
                throw new cce.UnreachableException();
            }
          }
          else {
            switch (op) {
              case BinaryExpr.ResolvedOpcode.Lt:
                opString = "<";
                break;
              case BinaryExpr.ResolvedOpcode.Le:
                opString = "<=";
                break;
              case BinaryExpr.ResolvedOpcode.Ge:
                opString = ">=";
                break;
              case BinaryExpr.ResolvedOpcode.Gt:
                opString = ">";
                break;
              default:
                Contract.Assert(false);
                throw new cce.UnreachableException();
            }
          }

          break;
        case BinaryExpr.ResolvedOpcode.LtChar:
          opString = "<";
          break;
        case BinaryExpr.ResolvedOpcode.LeChar:
          opString = "<=";
          break;
        case BinaryExpr.ResolvedOpcode.GeChar:
          opString = ">=";
          break;
        case BinaryExpr.ResolvedOpcode.GtChar:
          opString = ">";
          break;
        case BinaryExpr.ResolvedOpcode.LeftShift:
          doPossiblyNativeBinOp("<<", "shiftLeft", out preOpString, out opString, out postOpString, out callString);
          truncateResult = true;
          convertE1_to_int = AsNativeType(e1.Type) == null;
          break;
        case BinaryExpr.ResolvedOpcode.RightShift:
          doPossiblyNativeBinOp(">>>", "shiftRight", out preOpString, out opString, out postOpString, out callString);
          convertE1_to_int = AsNativeType(e1.Type) == null;
          break;
        case BinaryExpr.ResolvedOpcode.Add:
          truncateResult = true;
          if (resultType.IsCharType) {
            preOpString = "(char) (";
            postOpString = ")";
            opString = "+";
          }
          else {
            doPossiblyNativeBinOp("+", "add", out preOpString, out opString, out postOpString, out callString);
          }

          break;
        case BinaryExpr.ResolvedOpcode.Sub:
          truncateResult = true;
          if (resultType.IsCharType) {
            preOpString = "(char) (";
            opString = "-";
            postOpString = ")";
          }
          else {
            doPossiblyNativeBinOp("-", "subtract", out preOpString, out opString, out postOpString, out callString);
          }

          break;
        case BinaryExpr.ResolvedOpcode.Mul:
          doPossiblyNativeBinOp("*", "multiply", out preOpString, out opString, out postOpString, out callString);
          truncateResult = true;
          break;
        case BinaryExpr.ResolvedOpcode.Div:
          if (resultType.IsIntegerType ||
              (AsNativeType(resultType) != null && AsNativeType(resultType).LowerBound < BigInteger.Zero)) {
            var suffix = AsNativeType(resultType) != null ? "_" + GetNativeTypeName(AsNativeType(resultType)) : "";
            staticCallString = $"{DafnyEuclideanClass}.EuclideanDivision" + suffix;
          }
          else if (AsNativeType(resultType) != null) {
            preOpString = CastIfSmallNativeType(resultType);
            staticCallString = HelperClass(AsNativeType(resultType)) + ".divideUnsigned";
          }
          else {
            callString = "divide";
          }

          break;
        case BinaryExpr.ResolvedOpcode.Mod:
          if (resultType.IsIntegerType ||
              (AsNativeType(resultType) != null && AsNativeType(resultType).LowerBound < BigInteger.Zero)) {
            var suffix = AsNativeType(resultType) != null ? "_" + GetNativeTypeName(AsNativeType(resultType)) : "";
            staticCallString = $"{DafnyEuclideanClass}.EuclideanModulus" + suffix;
          }
          else if (AsNativeType(resultType) != null) {
            preOpString = CastIfSmallNativeType(resultType);
            staticCallString = HelperClass(AsNativeType(resultType)) + ".remainderUnsigned";
          }
          else {
            callString = "mod";
          }

          break;
        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
        case BinaryExpr.ResolvedOpcode.SeqEq:
        case BinaryExpr.ResolvedOpcode.MapEq:
          callString = "equals";
          break;
        case BinaryExpr.ResolvedOpcode.SetNeq:
        case BinaryExpr.ResolvedOpcode.MultiSetNeq:
        case BinaryExpr.ResolvedOpcode.SeqNeq:
        case BinaryExpr.ResolvedOpcode.MapNeq:
          preOpString = "!";
          callString = "equals";
          break;
        case BinaryExpr.ResolvedOpcode.ProperSubset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
          callString = "isProperSubsetOf";
          break;
        case BinaryExpr.ResolvedOpcode.Subset:
        case BinaryExpr.ResolvedOpcode.MultiSubset:
          callString = "isSubsetOf";
          break;
        case BinaryExpr.ResolvedOpcode.Superset:
        case BinaryExpr.ResolvedOpcode.MultiSuperset:
          callString = "isSubsetOf";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.ProperSuperset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
          callString = "IsProperSubsetOf";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.Disjoint:
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
          callString = "disjoint";
          break;
        case BinaryExpr.ResolvedOpcode.InSet:
        case BinaryExpr.ResolvedOpcode.InMultiSet:
        case BinaryExpr.ResolvedOpcode.InMap:
          callString = "contains";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.NotInSet:
        case BinaryExpr.ResolvedOpcode.NotInMultiSet:
        case BinaryExpr.ResolvedOpcode.NotInMap:
          preOpString = "!";
          callString = "contains";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
          callString = "union";
          break;
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          callString = "intersection";
          break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
          callString = "difference";
          break;

        case BinaryExpr.ResolvedOpcode.ProperPrefix:
          callString = "isProperPrefixOf";
          break;
        case BinaryExpr.ResolvedOpcode.Prefix:
          callString = "isPrefixOf";
          break;
        case BinaryExpr.ResolvedOpcode.Concat:
          callString = "concatenate";
          break;
        case BinaryExpr.ResolvedOpcode.InSeq:
          callString = "contains";
          reverseArguments = true;
          break;
        case BinaryExpr.ResolvedOpcode.NotInSeq:
          preOpString = "!";
          callString = "contains";
          reverseArguments = true;
          break;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException(); // unexpected binary expression
      }
    }

    public void CompileTuples(string path) {
      foreach (int i in tuples) {
        if (i == 2 || i == 3)
          continue; // Tuple2 and Tuple3 already exist in DafnyRuntime-1.jar, so don't remake these files.
        CreateTuple(i, path);
      }
    }

    private static void CreateTuple(int i, string path) {
      var wrTop = new TargetWriter();
      wrTop.WriteLine("package dafny;");
      wrTop.WriteLine();
      wrTop.Write("public class Tuple");
      wrTop.Write(i);
      if (i != 0) {
        wrTop.Write("<");
        for (int j = 0; j < i; j++) {
          wrTop.Write("T" + j);
          if (j != i - 1)
            wrTop.Write(", ");
          else {
            wrTop.Write(">");
          }
        }
      }

      var wr = wrTop.NewBlock("");
      for (int j = 0; j < i; j++) {
        wr.WriteLine("private T" + j + " _" + j + ";");
      }

      wr.WriteLine();

      wr.Write("public Tuple" + i + "(");
      for (int j = 0; j < i; j++) {
        wr.Write("T" + j + " _" + j);
        if (j != i - 1)
          wr.Write(", ");
      }

      using (var wrCtor = wr.NewBlock(")")) {
        for (int j = 0; j < i; j++) {
          wrCtor.WriteLine("this._" + j + " = _" + j + ";");
        }
      }

      wr.WriteLine($"private static final Tuple{i} DEFAULT = new Tuple{i}();");
      wr.WriteLine(
        $"private static final {TypeClass}<Tuple{i}> TYPE = {TypeClass}.referenceWithDefault(Tuple{i}.class, DEFAULT);");
      wr.WriteLine($"public static {TypeClass}<Tuple{i}> {TypeMethodName}() {{ return TYPE; }}");
      if (i != 0) {
        wr.WriteLine();
        wr.Write("public Tuple" + i + "() {}");
      }

      wr.WriteLine();
      wr.WriteLine("@Override");
      using (var wrEquals = wr.NewBlock("public boolean equals(Object obj)")) {
        wrEquals.WriteLine("if (this == obj) return true;");
        wrEquals.WriteLine("if (obj == null) return false;");
        wrEquals.WriteLine("if (getClass() != obj.getClass()) return false;");
        wrEquals.WriteLine($"Tuple{i} o = (Tuple{i}) obj;");
        if (i != 0) {
          wrEquals.Write("return ");
          for (int j = 0; j < i; j++) {
            wrEquals.Write("this._" + j + ".equals(o._" + j + ")");
            if (j != i - 1)
              wrEquals.Write(" && ");
            else {
              wrEquals.WriteLine(";");
            }
          }
        }
        else {
          wrEquals.WriteLine("return true;");
        }
      }

      wr.WriteLine();
      wr.WriteLine("@Override");
      using (var wrToString = wr.NewBlock("public String toString()")) {
        wrToString.WriteLine("StringBuilder sb = new StringBuilder();");
        wrToString.WriteLine("sb.append(\"(\");");
        for (int j = 0; j < i; j++) {
          wrToString.WriteLine($"sb.append(_{j} == null ? \"\" : _{j}.toString());");
          if (j != i - 1)
            wrToString.WriteLine("sb.append(\", \");");
        }

        wrToString.WriteLine("sb.append(\")\");");
        wrToString.WriteLine("return sb.toString();");
      }

      wr.WriteLine();
      wr.WriteLine("@Override");
      using (var wrHashCode = wr.NewBlock("public int hashCode()")) {
        wrHashCode.WriteLine("// GetHashCode method (Uses the djb2 algorithm)");
        wrHashCode.WriteLine(
          "// https://stackoverflow.com/questions/1579721/why-are-5381-and-33-so-important-in-the-djb2-algorithm");
        wrHashCode.WriteLine("long hash = 5381;");
        wrHashCode.WriteLine("hash = ((hash << 5) + hash) + 0;");
        for (int j = 0; j < i; j++) {
          wrHashCode.WriteLine("hash = ((hash << 5) + hash) + ((long) this._" + j + ".hashCode());");
        }

        wrHashCode.WriteLine("return (int) hash;");
      }

      for (int j = 0; j < i; j++) {
        wr.WriteLine();
        wr.WriteLine("public T" + j + " dtor__" + j + "() { return this._" + j + "; }");
      }

      // Create a file to write to.
      using (StreamWriter sw = File.CreateText(path + "/Tuple" + i + ".java")) {
        sw.Write(wrTop.ToString());
      }
    }

    public override string TypeInitializationValue(Type type, TextWriter wr, Bpl.IToken tok, bool inAutoInitContext) {
      var xType = type.NormalizeExpandKeepConstraints();
      if (xType is BoolType) {
        return "false";
      }
      else if (xType is CharType) {
        return "'D'";
      }
      else if (xType is IntType || xType is BigOrdinalType) {
        return "java.math.BigInteger.ZERO";
      }
      else if (xType is RealType) {
        return $"{DafnyBigRationalClass}.ZERO";
      }
      else if (xType is BitvectorType) {
        var t = (BitvectorType) xType;
        return t.NativeType != null ? $"{CastIfSmallNativeType(t)}0" : "java.math.BigInteger.ZERO";
      }
      else if (xType is CollectionType collType) {
        string collName = CollectionTypeUnparameterizedName(collType);
        string argNames = BoxedTypeName(collType.Arg, wr, tok);
        if (xType is MapType mapType) {
          argNames += "," + BoxedTypeName(mapType.Range, wr, tok);
        }

        string td = "";
        if (xType is SeqType) {
          td = TypeDescriptor(collType.Arg, wr, tok);
        }

        return $"{collName}.<{argNames}> empty({td})";
      }

      var udt = (UserDefinedType) xType;
      if (udt.ResolvedParam != null) {
        if (inAutoInitContext && !udt.ResolvedParam.Characteristics.MustSupportZeroInitialization) {
          return "null";
        }
        else {
          return $"{FormatTypeDescriptorVariable(udt.ResolvedParam.CompileName)}.defaultValue()";
        }
      }

      var cl = udt.ResolvedClass;
      Contract.Assert(cl != null);
      if (cl is NewtypeDecl) {
        var td = (NewtypeDecl) cl;
        if (td.Witness != null) {
          return FullTypeName(udt) + ".Witness";
        }
        else if (td.NativeType != null) {
          return GetNativeDefault(td.NativeType);
        }
        else {
          return TypeInitializationValue(td.BaseType, wr, tok, inAutoInitContext);
        }
      }
      else if (cl is SubsetTypeDecl) {
        var td = (SubsetTypeDecl) cl;
        if (td.Witness != null) {
          return FullTypeName(udt) + ".Witness";
        }
        else if (td.WitnessKind == SubsetTypeDecl.WKind.Special) {
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) ||
                          td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            return $"(({BoxedTypeName(xType, wr, udt.tok)}) null)";
          }
          else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            var rangeDefaultValue = TypeInitializationValue(udt.TypeArgs.Last(), wr, tok, inAutoInitContext);
            // return the lambda expression ((Ty0 x0, Ty1 x1, Ty2 x2) -> rangeDefaultValue)
            return
              $"(({Util.Comma(", ", udt.TypeArgs.Count - 1, i => $"{BoxedTypeName(udt.TypeArgs[i], wr, udt.tok)} x{i}")}) -> {rangeDefaultValue})";
          }
          else if (((NonNullTypeDecl) td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            var arrayClass = (ArrayClassDecl) ((NonNullTypeDecl) td).Class;
            string newarr = "";
            string bareArray;
            var elType = udt.TypeArgs[0];

            if (elType.IsTypeParameter) {
              bareArray =
                $"(Object{Util.Repeat("[]", arrayClass.Dims - 1)}) {TypeDescriptor(elType, wr, tok)}.newArray({Util.Comma(Enumerable.Repeat("0", arrayClass.Dims))})";
            }
            else {
              bareArray = $"new {TypeName(elType, wr, tok)}{Util.Repeat("[0]", arrayClass.Dims)}";
            }

            if (arrayClass.Dims > 1) {
              arrays.Add(arrayClass.Dims);
              newarr += $"new {DafnyMultiArrayClass(arrayClass.Dims)}<>({TypeDescriptor(elType, wr, tok)}, ";
              for (int i = 0; i < arrayClass.Dims; i++) {
                newarr += "0, ";
              }

              newarr += $"{bareArray})";
            }
            else {
              newarr = bareArray;
            }

            return newarr;
          }
          else {
            return "null";
          }
        }
        else {
          return TypeInitializationValue(td.RhsWithArgument(udt.TypeArgs), wr, tok, inAutoInitContext);
        }
      }
      else if (cl is ClassDecl) {
        bool isHandle = true;
        if (Attributes.ContainsBool(cl.Attributes, "handle", ref isHandle) && isHandle) {
          return "0";
        }
        else {
          return $"({BoxedTypeName(xType, wr, udt.tok)}) null";
        }
      }
      else if (cl is DatatypeDecl dt) {
        var s = FullTypeName(udt);
        var typeargs = "";
        if (udt.TypeArgs.Count != 0) {
          typeargs = $"<{BoxedTypeNames(udt.TypeArgs, wr, udt.tok)}>";
        }

        // In an auto-init context (like a field initializer), we may not have
        // access to all the type descriptors, so we can't construct the
        // default value, but then null is always an acceptable default in
        // such contexts (since Dafny proves the null won't be accessed).
        if (cl is TupleTypeDecl || inAutoInitContext) {
          return $"({s}{typeargs})null";
        }

        UsedTypeParameters(dt, udt.TypeArgs, out _, out var usedTypeArgs);
        return $"{s}.{typeargs}Default({Util.Comma(usedTypeArgs, ta => TypeDescriptor(ta, wr, tok))})";
      }
      else {
        Contract.Assert(false);
        throw new cce.UnreachableException(); // unexpected type
      }
    }

    protected override TargetWriter DeclareLocalVar(string name, Type type, Bpl.IToken tok, TargetWriter wr) {
      wr.Write("{0} {1} = ", type != null ? TypeName(type, wr, tok) : "var", name);
      var w = wr.Fork();
      wr.WriteLine(";");
      return w;
    }

    protected override void DeclareLocalOutVar(string name, Type type, Bpl.IToken tok, string rhs,
      bool useReturnStyleOuts, TargetWriter wr) {
      DeclareLocalVar(name, type, tok, false, rhs, wr);
    }

    protected override IClassWriter CreateTrait(string name, bool isExtern, List<Type> superClasses, Bpl.IToken tok,
      TargetWriter wr) {
      var filename = $"{ModulePath}/{name}.java";
      var w = wr.NewFile(filename);
      FileCount += 1;
      w.WriteLine($"// Interface {name}");
      w.WriteLine($"// Dafny trait {name} compiled into Java");
      w.WriteLine($"package {ModuleName};");
      w.WriteLine();
      EmitImports(w, out _);
      w.WriteLine();
      EmitSuppression(w); //TODO: Fix implementations so they do not need this suppression
      w.Write($"public interface {IdProtect(name)}");
      if (superClasses != null) {
        string sep = " implements ";
        foreach (var trait in superClasses) {
          w.Write($"{sep}{TypeName(trait, w, tok)}");
          sep = ", ";
        }
      }

      var instanceMemberWriter = w.NewBlock("");
      //writing the _Companion class
      filename = $"{ModulePath}/_Companion_{name}.java";
      w = w.NewFile(filename);
      FileCount += 1;
      w.WriteLine($"// Interface {name}");
      w.WriteLine($"// Dafny trait {name} compiled into Java");
      w.WriteLine($"package {ModuleName};");
      w.WriteLine();
      EmitImports(w, out _);
      w.WriteLine();
      w.Write($"public class _Companion_{name}");
      var staticMemberWriter = w.NewBlock("");
      var ctorBodyWriter = staticMemberWriter.NewBlock($"public _Companion_{name}()");
      //return new ClassWriter(this, instanceMemberWriter, ctorBodyWriter, staticMemberWriter);
      return null;
    }

    protected override void EmitDestructor(string source, Formal dtor, int formalNonGhostIndex, DatatypeCtor ctor,
      List<Type> typeArgs, Type bvType, TargetWriter wr) {
      string dtorName;
      if (ctor.EnclosingDatatype is TupleTypeDecl) {
        dtorName = $"dtor__{dtor.Name}()";
      }
      else if (int.TryParse(dtor.Name, out _)) {
        dtorName = $"dtor_{dtor.Name}()";
      }
      else {
        dtorName = FormalName(dtor, formalNonGhostIndex);
      }

      wr.Write("(({0}){1}{2}).{3}", DtCtorName(ctor, typeArgs, wr), source,
        ctor.EnclosingDatatype is CoDatatypeDecl ? ".Get()" : "", dtorName);
    }

    public void CreateFunctionInterface(string path) {
      foreach (int i in functions) {
        CreateLambdaFunctionInterface(i, path);
      }
    }

    public void CreateLambdaFunctionInterface(int i, string path) {
      var typeArgs = "<";
      for (int j = 0; j < i + 1; j++) {
        typeArgs += "T" + j;
        if (j != i) {
          typeArgs += ", ";
        }
      }

      typeArgs += ">";

      var wr = new TargetWriter();
      wr.WriteLine("package dafny;");
      wr.WriteLine();
      wr.WriteLine("@FunctionalInterface");
      wr.Write("public interface Function");
      wr.Write(i);
      wr.Write(typeArgs);
      var wrMembers = wr.NewBlock("");
      wrMembers.Write("public T" + i + " apply(");
      for (int j = 0; j < i; j++) {
        wrMembers.Write("T" + j + " t" + j);
        if (j != i - 1)
          wrMembers.Write(", ");
      }

      wrMembers.WriteLine(");");

      EmitSuppression(wrMembers);
      wrMembers.Write($"public static {typeArgs} {TypeClass}<Function{i}{typeArgs}> {TypeMethodName}(");
      for (int j = 0; j < i + 1; j++) {
        wrMembers.Write($"{TypeClass}<T{j}> t{j}");
        if (j != i) {
          wrMembers.Write(", ");
        }
      }

      var wrTypeBody = wrMembers.NewBigBlock(")", "");
      // XXX This seems to allow non-nullable types to have null values (since
      // arrow types are allowed as "(0)"-constrained type arguments), but it's
      // consistent with other backends.
      wrTypeBody.Write(
        $"return ({TypeClass}<Function{i}{typeArgs}>) ({TypeClass}<?>) {TypeClass}.reference(Function{i}.class);");

      using (StreamWriter sw = File.CreateText(path + "/Function" + i + ".java")) {
        sw.Write(wr.ToString());
      }
    }

    public void CompileDafnyArrays(string path) {
      foreach (int i in arrays) {
        CreateDafnyArrays(i, path);
      }
    }

    public void CreateDafnyArrays(int i, string path) {
      var wrTop = new TargetWriter();
      wrTop.WriteLine("package dafny;");
      wrTop.WriteLine();

      // All brackets on the underlying "real" array type, minus the innermost
      // pair.  The innermost array must be represented as an Object since it
      // could be of primitive type.
      var outerBrackets = Util.Repeat("[]", i - 1);

      var dims = Enumerable.Range(0, i);
      var outerDims = Enumerable.Range(0, i - 1);

      var wr = wrTop.NewBlock($"public final class Array{i}<T>");

      wr.WriteLine($"public final Object{outerBrackets} elmts;");
      wr.WriteLine($"private final {TypeClass}<T> elmtType;");

      foreach (var j in dims) {
        wr.WriteLine($"public final int dim{j};");
      }

      using (var wrBody =
        wr.NewBlock(
          $"public Array{i}({TypeClass}<T> elmtType, {Util.Comma(dims, j => $"int dim{j}")}, Object{outerBrackets} elmts)")
      ) {
        wrBody.WriteLine("assert elmts.getClass().isArray();");
        wrBody.WriteLine("this.elmtType = elmtType;");
        foreach (var j in dims) {
          wrBody.WriteLine($"this.dim{j} = dim{j};");
        }

        wrBody.WriteLine("this.elmts = elmts;");
      }

      using (var wrBody = wr.NewBlock($"public T get({Util.Comma(dims, j => $"int i{j}")})")) {
        wrBody.Write("return elmtType.getArrayElement(elmts");
        foreach (var j in outerDims) {
          wrBody.Write($"[i{j}]");
        }

        wrBody.WriteLine($", i{i - 1});");
      }

      using (var wrBody = wr.NewBlock($"public void set({Util.Comma(dims, j => $"int i{j}")}, T value)")) {
        wrBody.Write("elmtType.setArrayElement(elmts");
        foreach (var j in outerDims) {
          wrBody.Write($"[i{j}]");
        }

        wrBody.WriteLine($", i{i - 1}, value);");
      }

      using (var body = wr.NewBlock("public void fill(T z)")) {
        var forBodyWr = body;
        for (int j = 0; j < i - 1; j++) {
          forBodyWr = forBodyWr.NewBlock($"for(int i{j} = 0; i{j} < dim{j}; i{j}++)");
        }

        forBodyWr.Write($"elmtType.fillArray(elmts");
        for (int j = 0; j < i - 1; j++) {
          forBodyWr.Write($"[i{j}]");
        }

        forBodyWr.WriteLine(", z);");
      }

      using (var body = wr.NewBlock($"public Array{i} fillThenReturn(T z)")) {
        body.WriteLine("fill(z);");
        body.WriteLine("return this;");
      }

      EmitSuppression(wr);
      wr.WriteLine(
        $"private static final {TypeClass}<Array{i}<?>> TYPE = ({TypeClass}<Array{i}<?>>) ({TypeClass}<?>) {TypeClass}.reference(Array{i}.class);");
      EmitSuppression(wr);
      var wrTypeMethod = wr.NewBlock($"public static <T> {TypeClass}<Array{i}<T>> {TypeMethodName}()");
      wrTypeMethod.WriteLine($"return ({TypeClass}<Array{i}<T>>) ({TypeClass}<?>) TYPE;");

      using (StreamWriter sw = File.CreateText(path + "/Array" + i + ".java")) {
        sw.Write(wrTop.ToString());
      }
    }

    protected override BlockTargetWriter EmitTailCallStructure(MemberDecl member, BlockTargetWriter wr) {
      if (!member.IsStatic && !NeedsCustomReceiver(member)) {
        var receiverType = UserDefinedType.FromTopLevelDecl(member.tok, member.EnclosingClass);
        var receiverTypeName = TypeName(receiverType, wr, member.tok);
        if (member.EnclosingClass.IsExtern(out _, out _)) {
          receiverTypeName = FormatExternBaseClassName(receiverTypeName);
        }

        wr.WriteLine("{0} _this = this;", receiverTypeName);
      }

      return wr.NewBlock("TAIL_CALL_START: while (true)");
    }

    protected override void EmitJumpToTailCallStart(TargetWriter wr) {
      wr.WriteLine("continue TAIL_CALL_START;");
    }

    protected override void EmitCollectionBuilder_New(CollectionType ct, Bpl.IToken tok, TargetWriter wr) {
      if (ct is SetType) {
        wr.Write("new java.util.ArrayList<>()");
      }
      else if (ct is MapType mt) {
        wr.Write($"new {DafnyMapClass}<>()");
      }
      else {
        Contract.Assume(false); // unexpected collection type
      }
    }

    protected override BlockTargetWriter CreateForeachLoop(string boundVar, Type boundVarType,
      out TargetWriter collectionWriter,
      TargetWriter wr, string altBoundVarName = null, Type altVarType = null, Bpl.IToken tok = null) {
      if (boundVarType != null) {
        wr.Write($"for({TypeName(boundVarType, wr, tok)} {boundVar} : ");
      }
      else {
        wr.Write($"for({DafnyTupleClass(TargetTupleSize)} {boundVar} : ");
      }

      collectionWriter = wr.Fork();
      if (altBoundVarName == null) {
        return wr.NewBlock(")");
      }
      else if (altVarType == null) {
        return wr.NewBlockWithPrefix(")", $"{altBoundVarName} = {boundVar};");
      }
      else {
        return wr.NewBlockWithPrefix(")", "{2} {0} = ({2}){1};", altBoundVarName, boundVar,
          TypeName(altVarType, wr, tok));
      }
    }

    protected override void EmitCollectionBuilder_Add(CollectionType ct, string collName, Expression elmt,
      bool inLetExprBody, TargetWriter wr) {
      if (ct is SetType) {
        wr.Write($"{collName}.add(");
        TrExpr(elmt, wr, inLetExprBody);
        wr.WriteLine(");");
      }
      else {
        Contract.Assume(false); // unepxected collection type
      }
    }

    protected override string GetCollectionBuilder_Build(CollectionType ct, Bpl.IToken tok, string collName,
      TargetWriter wr) {
      if (ct is SetType) {
        var typeName = BoxedTypeName(ct.Arg, wr, tok);
        return $"new dafny.DafnySet<{typeName}>({collName})";
      }
      else if (ct is MapType) {
        var mt = (MapType) ct;
        var domtypeName = BoxedTypeName(mt.Domain, wr, tok);
        var rantypeName = BoxedTypeName(mt.Range, wr, tok);
        return $"new {DafnyMapClass}<{domtypeName},{rantypeName}>({collName})";
      }
      else {
        Contract.Assume(false); // unexpected collection type
        throw new cce.UnreachableException(); // please compiler
      }
    }

    protected override TargetWriter CreateLabeledCode(string label, TargetWriter wr) {
      return wr.NewNamedBlock($"goto_{label}:");
    }

    protected override void EmitBreak(string label, TargetWriter wr) {
      wr.WriteLine(label == null ? "break;" : $"break goto_{label};");
    }

    protected override void EmitAbsurd(string message, TargetWriter wr) {
      if (message == null) {
        message = "unexpected control point";
      }

      wr.WriteLine($"throw new IllegalArgumentException(\"{message}\");");
    }

    protected override void EmitAbsurd(string message, TargetWriter wr, bool needIterLimit) {
      if (!needIterLimit) {
        EmitAbsurd(message, wr);
      }
    }

    protected override void EmitHalt(Expression messageExpr, TargetWriter wr) {
      wr.Write("throw new dafny.DafnyHaltException(");
      EmitToString(wr, messageExpr);
      wr.WriteLine(");");
    }

    protected override IClassWriter DeclareNewtype(NewtypeDecl nt, TargetWriter wr) {
      // var cw = CreateClass(IdName(nt), null, wr) as ClassWriter;
      // var w = cw.StaticMemberWriter;
      // if (nt.NativeType != null) {
      //   var nativeType = GetBoxedNativeTypeName(nt.NativeType);
      //   var wEnum = w.NewNamedBlock($"public static java.util.ArrayList<{nativeType}> IntegerRange(java.math.BigInteger lo, java.math.BigInteger hi)");
      //   wEnum.WriteLine($"java.util.ArrayList<{nativeType}> arr = new java.util.ArrayList<>();");
      //   var numberval = "intValue()";
      //   if (nativeType == "Byte" || nativeType == "Short")
      //     numberval = $"{nativeType.ToLower()}Value()";
      //   wEnum.WriteLine($"for (java.math.BigInteger j = lo; j.compareTo(hi) < 0; j.add(java.math.BigInteger.ONE)) {{ arr.add(new {nativeType}(j.{numberval})); }}");
      //   wEnum.WriteLine("return arr;");
      // }
      // if (nt.WitnessKind == SubsetTypeDecl.WKind.Compiled) {
      //   var witness = new TargetWriter(w.IndentLevel, true);
      //   TrExpr(nt.Witness, witness, false);
      //   if (nt.NativeType == null) {
      //     cw.DeclareField("Witness", true, true, nt.BaseType, nt.tok, witness.ToString());
      //   } else {
      //     var nativeType = GetNativeTypeName(nt.NativeType);
      //     // Hacky way of doing the conversion from any (including BigInteger) to any
      //     w.Write("public static {0} Witness = ((java.lang.Number) (", nativeType);
      //     w.Append(witness);
      //     w.WriteLine($")).{nativeType}Value();");
      //   }
      // }
      // return cw;
      return null;
    }

    // private void TrExprAsInt(Expression expr, TargetWriter wr, bool inLetExprBody) {
    //   // TODO: Optimize
    //   if (AsNativeType(expr.Type) == null) {
    //     TrParenExpr(expr, wr, inLetExprBody);
    //     wr.Write(".intValue()");
    //   }
    //   else {
    //     TrExpr(expr, wr, inLetExprBody);
    //   }
    // }
    //
    // private void TrParenExprAsInt(Expression expr, TargetWriter wr, bool inLetExprBody) {
    //   wr.Write('(');
    //   TrExprAsInt(expr, wr, inLetExprBody);
    //   wr.Write(')');
    // }
    //
    // private void TrParenExprAsInt(string prefix, Expression expr, TargetWriter wr, bool inLetExprBody) {
    //   wr.Write(prefix);
    //   TrParenExprAsInt(expr, wr, inLetExprBody);
    // }

     protected override void EmitNewArray(Type elmtType, Bpl.IToken tok, List<Expression> dimensions,
       bool mustInitialize, TargetWriter wr) {
    //   // Where to put the array to be wrapped
    //   TargetWriter wBareArray;
    //   if (dimensions.Count > 1) {
    //     arrays.Add(dimensions.Count);
    //     wr.Write($"new {DafnyMultiArrayClass(dimensions.Count)}<>({TypeDescriptor(elmtType, wr, tok)}, ");
    //     foreach (var dim in dimensions) {
    //       TrExprAsInt(dim, wr, inLetExprBody: false);
    //       wr.Write(", ");
    //     }
    //
    //     wBareArray = wr.Fork();
    //     wr.Write(")");
    //     if (mustInitialize) {
    //       wr.Write($".fillThenReturn({DefaultValue(elmtType, wr, tok)})");
    //     }
    //   }
    //   else {
    //     if (!elmtType.IsTypeParameter) {
    //       wr.Write($"({ArrayTypeName(elmtType, dimensions.Count, wr, tok)}) ");
    //     }
    //
    //     if (mustInitialize) {
    //       wr.Write($"{TypeDescriptor(elmtType, wr, tok)}.fillThenReturnArray(");
    //     }
    //
    //     wBareArray = wr.Fork();
    //     if (mustInitialize) {
    //       wr.Write($", {DefaultValue(elmtType, wr, tok)})");
    //     }
    //   }
    //
    //   if (elmtType.IsTypeParameter) {
    //     if (dimensions.Count > 1) {
    //       wBareArray.Write($"(Object{Util.Repeat("[]", dimensions.Count - 1)}) ");
    //     }
    //
    //     wBareArray.Write($"{TypeDescriptor(elmtType, wr, tok)}.newArray(");
    //     var sep = "";
    //     foreach (var dim in dimensions) {
    //       wBareArray.Write(sep);
    //       TrExprAsInt(dim, wBareArray, inLetExprBody: false);
    //       sep = ", ";
    //     }
    //
    //     wBareArray.Write(")");
    //   }
    //   else {
    //     wBareArray.Write($"new {TypeName(elmtType, wr, tok)}");
    //     foreach (var dim in dimensions) {
    //       wBareArray.Write("[");
    //       TrExprAsInt(dim, wBareArray, inLetExprBody: false);
    //       wBareArray.Write("]");
    //     }
    //   }
     }

    protected override int EmitRuntimeTypeDescriptorsActuals(List<Type> typeArgs, List<TypeParameter> formals,
      Bpl.IToken tok, bool useAllTypeArgs, TargetWriter wr) {
      var sep = "";
      var c = 0;
      for (int i = 0; i < typeArgs.Count; i++) {
        var actual = typeArgs[i];
        var formal = formals[i];
        // Ignore useAllTypeArgs; we always need all of them
        wr.Write(sep);
        wr.Write(TypeDescriptor(actual, wr, tok));
        sep = ", ";
        c++;
      }

      return c;
    }

    protected override TargetWriter EmitBetaRedex(List<string> boundVars, List<Expression> arguments, string typeArgs,
      List<Type> boundTypes, Type resultType, Bpl.IToken resultTok, bool inLetExprBody, TargetWriter wr) {
      if (boundTypes.Count != 1) {
        functions.Add(boundTypes.Count);
      }

      wr.Write("(({0}<{1}{2}>)", DafnyFunctionIface(boundTypes.Count),
        Util.Comma("", boundTypes, t => BoxedTypeName(t, wr, resultTok) + ", "),
        BoxedTypeName(resultType, wr, resultTok));
      wr.Write($"({Util.Comma(boundVars)}) -> ");
      var w = wr.Fork();
      wr.Write(").apply");
      TrExprList(arguments, wr, inLetExprBody);
      return w;
    }

    protected override BlockTargetWriter CreateForLoop(string indexVar, string bound, TargetWriter wr) {
      return wr.NewNamedBlock(
        $"for (java.math.BigInteger {indexVar} = java.math.BigInteger.ZERO; {indexVar}.compareTo({bound}) < 0; {indexVar} = {indexVar}.add(java.math.BigInteger.ONE))");
    }

    protected override string GetHelperModuleName() => DafnyHelpersClass;

    protected override void EmitEmptyTupleList(string tupleTypeArgs, TargetWriter wr) {
      wr.WriteLine("new java.util.ArrayList<>();");
    }

    protected override void AddTupleToSet(int i) {
      tuples.Add(i);
    }

    protected override TargetWriter EmitAddTupleToList(string ingredients, string tupleTypeArgs, TargetWriter wr) {
      // FIXME: tupleTypeArgs is wrong because it already got generated from
      // TypeName (with unboxed being the default)  :-(
      wr.Write($"{ingredients}.add(new {DafnyTupleClassPrefix}");
      var wrTuple = wr.Fork();
      wr.Write("));");
      return wrTuple;
    }

    protected override void EmitExprAsInt(Expression expr, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(expr, wr, inLetExprBody);
      wr.Write(".intValue()");
    }

    protected override void EmitTupleSelect(string prefix, int i, TargetWriter wr) {
      wr.Write($"{prefix}.dtor__{i}()");
    }

    protected override void EmitApplyExpr(Type functionType, Bpl.IToken tok, Expression function,
      List<Expression> arguments, bool inLetExprBody, TargetWriter wr) {
      TrParenExpr(function, wr, inLetExprBody);
      wr.Write(".apply");
      TrExprList(arguments, wr, inLetExprBody);
    }

    protected override TargetWriter EmitCoercionToNativeInt(TargetWriter wr) {
      wr.Write("((java.math.BigInteger)");
      var w = wr.Fork();
      wr.Write(").intValue()");
      return w;
    }

    protected override BlockTargetWriter CreateDoublingForLoop(string indexVar, int start, TargetWriter wr) {
      return wr.NewNamedBlock(
        $"for (java.math.BigInteger {indexVar} = java.math.BigInteger.valueOf({start}); ; {indexVar} = {indexVar}.multiply(new java.math.BigInteger(\"2\")))");
    }

    protected override void EmitIsZero(string varName, TargetWriter wr) {
      wr.Write($"{varName}.equals(java.math.BigInteger.ZERO)");
    }

    protected override void EmitDecrementVar(string varName, TargetWriter wr) {
      wr.WriteLine($"{varName} = {varName}.subtract(java.math.BigInteger.ONE);");
    }

    protected override void EmitIncrementVar(string varName, TargetWriter wr) {
      wr.WriteLine($"{varName} = {varName}.add(java.math.BigInteger.ONE);");
    }

    protected override void EmitSingleValueGenerator(Expression e, bool inLetExprBody, string type, TargetWriter wr) {
      wr.Write("java.util.Arrays.asList");
      TrParenExpr(e, wr, inLetExprBody);
    }

    protected override BlockTargetWriter CreateIIFE1(int source, Type resultType, Bpl.IToken resultTok, string bvName,
      TargetWriter wr) {
      wr.Write(
        $"((java.util.function.Function<java.math.BigInteger, {BoxedTypeName(resultType, wr, resultTok)}>)(({bvName}) ->");
      var w = wr.NewBigExprBlock("", $")).apply(java.math.BigInteger.valueOf({source}))");
      return w;
    }

    protected override TargetWriter EmitMapBuilder_Add(MapType mt, Bpl.IToken tok, string collName, Expression term,
      bool inLetExprBody, TargetWriter wr) {
      wr.Write($"{collName}.put(");
      var termLeftWriter = wr.Fork();
      wr.Write(",");
      TrExpr(term, wr, inLetExprBody);
      wr.WriteLine(");");
      return termLeftWriter;
    }

    protected override void EmitSeqConstructionExpr(SeqConstructionExpr expr, bool inLetExprBody, TargetWriter wr) {
      wr.Write($"{DafnySeqClass}.Create({TypeDescriptor(expr.Type.AsCollectionType.Arg, wr, expr.tok)}, ");
      TrExpr(expr.N, wr, inLetExprBody);
      wr.Write(", ");
      TrExpr(expr.Initializer, wr, inLetExprBody);
      wr.Write(")");
    }

    // Warning: NOT the same as NativeType.Bitwidth, which is zero except for
    // bitvector types
    private static int NativeTypeSize(NativeType nt) {
      switch (AsJavaNativeType(nt)) {
        case JavaNativeType.Byte: return 8;
        case JavaNativeType.Short: return 16;
        case JavaNativeType.Int: return 32;
        case JavaNativeType.Long: return 64;
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();
      }
    }

    protected override void EmitConversionExpr(ConversionExpr e, bool inLetExprBody, TargetWriter wr) {
      // if (e.E.Type.IsNumericBased(Type.NumericPersuation.Int) || e.E.Type.IsBitVectorType || e.E.Type.IsCharType) {
      //   if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
      //     // (int or bv) -> real
      //     Contract.Assert(AsNativeType(e.ToType) == null);
      //     wr.Write($"new {DafnyBigRationalClass}(");
      //     if (AsNativeType(e.E.Type) != null) {
      //       wr.Write("java.math.BigInteger.valueOf");
      //     }
      //
      //     TrParenExpr(e.E, wr, inLetExprBody);
      //     wr.Write(", java.math.BigInteger.ONE)");
      //   }
      //   else if (e.ToType.IsCharType) {
      //     // Painfully, Java sign-extends bytes when casting to chars ...
      //     var fromNative = AsNativeType(e.E.Type);
      //     wr.Write("(char)");
      //     if (fromNative != null && fromNative.Sel == NativeType.Selection.Byte) {
      //       wr.Write("java.lang.Byte.toUnsignedInt");
      //       TrParenExpr(e.E, wr, inLetExprBody);
      //     }
      //     else {
      //       TrExprAsInt(e.E, wr, inLetExprBody);
      //     }
      //   }
      //   else {
      //     // (int or bv or char) -> (int or bv or ORDINAL)
      //     var fromNative = AsNativeType(e.E.Type);
      //     var toNative = AsNativeType(e.ToType);
      //     if (fromNative == null && toNative == null) {
      //       if (e.E.Type.IsCharType) {
      //         // char -> big-integer (int or bv or ORDINAL)
      //         wr.Write("java.math.BigInteger.valueOf");
      //         TrParenExpr(e.E, wr, inLetExprBody);
      //       }
      //       else {
      //         // big-integer (int or bv) -> big-integer (int or bv or ORDINAL), so identity will do
      //         TrExpr(e.E, wr, inLetExprBody);
      //       }
      //     }
      //     else if (fromNative != null && toNative == null) {
      //       // native (int or bv) -> big-integer (int or bv)
      //       if (fromNative.Sel == NativeType.Selection.ULong) {
      //         // Can't just use .longValue() because that may return a negative
      //         wr.Write($"{DafnyHelpersClass}.unsignedLongToBigInteger");
      //         TrParenExpr(e.E, wr, inLetExprBody);
      //       }
      //       else {
      //         wr.Write("java.math.BigInteger.valueOf(");
      //         if (fromNative.LowerBound >= 0) {
      //           TrParenExpr($"{GetBoxedNativeTypeName(fromNative)}.toUnsignedLong", e.E, wr, inLetExprBody);
      //         }
      //         else {
      //           TrParenExpr(e.E, wr, inLetExprBody);
      //         }
      //
      //         wr.Write(")");
      //       }
      //     }
      //     else if (fromNative != null && NativeTypeSize(toNative) == NativeTypeSize(fromNative)) {
      //       // native (int or bv) -> native (int or bv)
      //       // Cast between signed and unsigned, which have the same Java type
      //       TrParenExpr(e.E, wr, inLetExprBody);
      //     }
      //     else {
      //       GetNativeInfo(toNative.Sel, out var toNativeName, out var toNativeSuffix, out var toNativeNeedsCast);
      //       // any (int or bv) -> native (int or bv)
      //       // A cast would do, but we also consider some optimizations
      //       var literal = PartiallyEvaluate(e.E);
      //       UnaryOpExpr u = e.E.Resolved as UnaryOpExpr;
      //       MemberSelectExpr m = e.E.Resolved as MemberSelectExpr;
      //       if (literal != null) {
      //         // Optimize constant to avoid intermediate BigInteger
      //         EmitNativeIntegerLiteral((BigInteger) literal, toNative, wr);
      //       }
      //       else if (u != null && u.Op == UnaryOpExpr.Opcode.Cardinality) {
      //         // Optimize || to avoid intermediate BigInteger
      //         wr.Write(CastIfSmallNativeType(e.ToType));
      //         TrParenExpr("", u.E, wr, inLetExprBody);
      //         wr.Write(".cardinalityInt()");
      //       }
      //       else if (m != null && m.MemberName == "Length" && m.Obj.Type.IsArrayType) {
      //         // Optimize .length to avoid intermediate BigInteger
      //         wr.Write(CastIfSmallNativeType(e.ToType));
      //         var elmtType = UserDefinedType.ArrayElementType(m.Obj.Type);
      //         TargetWriter w;
      //         if (elmtType.IsTypeParameter) {
      //           wr.Write($"{FormatTypeDescriptorVariable(elmtType.AsTypeParameter)}.getArrayLength(");
      //           w = wr.Fork();
      //           wr.Write(")");
      //         }
      //         else {
      //           w = wr.Fork();
      //           wr.Write(".length");
      //         }
      //
      //         TrParenExpr(m.Obj, w, inLetExprBody);
      //       }
      //       else {
      //         // no optimization applies; use the standard translation
      //         if (fromNative != null && fromNative.LowerBound >= 0 &&
      //             NativeTypeSize(fromNative) < NativeTypeSize(toNative)) {
      //           // Widening an unsigned value; careful!!
      //           wr.Write($"{CastIfSmallNativeType(e.ToType)}{GetBoxedNativeTypeName(fromNative)}");
      //           if (NativeTypeSize(toNative) == 64) {
      //             wr.Write(".toUnsignedLong");
      //           }
      //           else {
      //             wr.Write(".toUnsignedInt");
      //           }
      //
      //           TrParenExpr(e.E, wr, inLetExprBody);
      //         }
      //         else {
      //           if (fromNative == null && !e.E.Type.IsCharType) {
      //             TrParenExpr(e.E, wr, inLetExprBody);
      //             wr.Write($".{toNativeName}Value()");
      //           }
      //           else {
      //             wr.Write($"(({toNativeName}) ");
      //             TrParenExpr(e.E, wr, inLetExprBody);
      //             wr.Write(")");
      //           }
      //         }
      //       }
      //     }
      //   }
      // }
      // else if (e.E.Type.IsNumericBased(Type.NumericPersuation.Real)) {
      //   Contract.Assert(AsNativeType(e.E.Type) == null);
      //   if (e.ToType.IsNumericBased(Type.NumericPersuation.Real)) {
      //     // real -> real
      //     Contract.Assert(AsNativeType(e.ToType) == null);
      //     TrExpr(e.E, wr, inLetExprBody);
      //   }
      //   else if (e.ToType.IsCharType) {
      //     // real -> char
      //     // Painfully, Java sign-extends bytes when casting to chars ...
      //     wr.Write("(char)");
      //     TrParenExpr(e.E, wr, inLetExprBody);
      //     wr.Write(".ToBigInteger().intValue()");
      //   }
      //   else {
      //     // real -> (int or bv)
      //     TrParenExpr(e.E, wr, inLetExprBody);
      //     wr.Write(".ToBigInteger()");
      //     if (AsNativeType(e.ToType) != null) {
      //       wr.Write($".{GetNativeTypeName(AsNativeType(e.ToType))}Value()");
      //     }
      //   }
      // }
      // else {
      //   Contract.Assert(e.E.Type.IsBigOrdinalType);
      //   Contract.Assert(e.ToType.IsNumericBased(Type.NumericPersuation.Int));
      //   TrParenExpr(e.E, wr, inLetExprBody);
      //   if (AsNativeType(e.ToType) != null) {
      //     wr.Write($".{GetNativeTypeName(AsNativeType(e.ToType))}Value()");
      //   }
      // }
    }

    protected override BlockTargetWriter CreateStaticMain(IClassWriter cw) {
      // var wr = ((ClassWriter) cw).StaticMemberWriter;
      // return wr.NewBlock("public static void Main(string[] args)");
      return null;
    }

    protected override TargetWriter CreateIIFE_ExprBody(string source, Type sourceType, Bpl.IToken sourceTok,
      Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      wr.Write($"{DafnyHelpersClass}.Let(");
      wr.Write($"{source}, {bvName} -> ");
      var w = wr.Fork();
      wr.Write(")");
      return w;
    }

    protected override TargetWriter CreateIIFE_ExprBody(Expression source, bool inLetExprBody, Type sourceType,
      Bpl.IToken sourceTok,
      Type resultType, Bpl.IToken resultTok, string bvName, TargetWriter wr) {
      wr.Write($"{DafnyHelpersClass}.Let(");
      TrExpr(source, wr, inLetExprBody);
      wr.Write($", {bvName} -> ");
      var w = wr.Fork();
      wr.Write(")");
      return w;
    }

    protected override string GetQuantifierName(string bvType) {
      return $"{DafnyHelpersClass}.Quantifier";
    }

    // ABSTRACT METHOD DECLARATIONS FOR THE SAKE OF BUILDING PROGRAM

    protected override void EmitYield(TargetWriter wr) {
      throw new NotImplementedException();
    }

    protected override BlockTargetWriter CreateIterator(IteratorDecl iter, TargetWriter wr) {
      throw new NotImplementedException();
    }


    AST.Statement TrStmt(Statement stmt) {
      Contract.Requires(stmt != null);
      Contract.Requires(errorWr != null);

      if (stmt.IsGhost) {
        Console.WriteLine("Not implemented: ghost statement"); // TODO
        // var v = new CheckHasNoAssumes_Visitor(this, wr);
        // v.Visit(stmt);
        return null;
      }

      if (stmt is PrintStmt) {
        Console.WriteLine("Not implemented: print statement");
        return null;  // TODO
        // var s = (PrintStmt) stmt;
        // foreach (var arg in s.Args) {
        //   EmitPrintStmt(wr, arg);
        // }
      } else if (stmt is BreakStmt) {
        return new AST.CommentStatement("Not implemented: break statement");
        // var s = (BreakStmt) stmt;
        // EmitBreak(s.TargetStmt.Labels.Data.AssignUniqueId(idGenerator), wr);
      } else if (stmt is ReturnStmt) {
        ReturnStmt p = (ReturnStmt) stmt;
        AssignmentRhs r = p.rhss.First();
        if (r is ExprRhs) {
          ExprRhs erhs = (ExprRhs) r;
          return new AST.ReturnStatement(TrExpr(erhs.Expr));
        } else if (r is TypeRhs) {
          TypeRhs tr = (TypeRhs)r;
          Expression f = tr.ArrayDimensions.First();
          AST.Expression e = new AST.NewArray(TrType(tr.EType), TrExpr(f));
          return new AST.ReturnStatement(e);
        } else {
          AST.Expression e = new AST.CommentExpr("Not implemented kind of AssignmentRhs");
          return new AST.ReturnStatement(e);
        }
      } else if (stmt is YieldStmt) {
        YieldStmt p = (YieldStmt) stmt;
        AssignmentRhs r = p.rhss.First();
        AST.Expression e = TrAssignmentRhs(r);
        return new AST.ReturnStatement(e);
        
        //   var s = (ProduceStmt) stmt;
        //   if (s.hiddenUpdate != null) {
        //     TrStmt(s.hiddenUpdate, wr);
        //   }
        //
        //   if (s is YieldStmt) {
        //     EmitYield(wr);
        //   }
        //   else {
        //     EmitReturn(this.enclosingMethod.Outs, wr);
        //   }
        // } else if (stmt is UpdateStmt) {
        //   var s = (UpdateStmt) stmt;
        //   var resolved = s.ResolvedStatements;
        //   if (resolved.Count == 1) {
        //     TrStmt(resolved[0], wr);
        //   }
        //   else {
        //     // multi-assignment
        //     Contract.Assert(s.Lhss.Count == resolved.Count);
        //     Contract.Assert(s.Rhss.Count == resolved.Count);
        //     var lhsTypes = new List<Type>();
        //     var rhsTypes = new List<Type>();
        //     var lhss = new List<Expression>();
        //     var rhss = new List<AssignmentRhs>();
        //     for (int i = 0; i < resolved.Count; i++) {
        //       if (!resolved[i].IsGhost) {
        //         var lhs = s.Lhss[i];
        //         var rhs = s.Rhss[i];
        //         if (rhs is HavocRhs) {
        //           if (DafnyOptions.O.ForbidNondeterminism) {
        //             Error(rhs.Tok, "nondeterministic assignment forbidden by /definiteAssignment:3 option", wr);
        //           }
        //         }
        //         else {
        //           lhss.Add(lhs);
        //           lhsTypes.Add(lhs.Type);
        //           rhss.Add(rhs);
        //           rhsTypes.Add(TypeOfRhs(rhs));
        //         }
        //       }
        //     }
        //
        //     var wStmts = wr.ForkSection();
        //     var lvalues = new List<ILvalue>();
        //     foreach (Expression lhs in lhss) {
        //       lvalues.Add(CreateLvalue(lhs, wStmts));
        //     }
        //
        //     List<TargetWriter> wRhss;
        //     EmitMultiAssignment(lvalues, lhsTypes, out wRhss, rhsTypes, wr);
        //     for (int i = 0; i < wRhss.Count; i++) {
        //       TrRhs(rhss[i], wRhss[i], wStmts);
        //     }
        //   }
      } else if (stmt is UpdateStmt) {
        UpdateStmt s = (UpdateStmt) stmt;
        AST.Expression lhs = TrExpr(s.Lhss.First());
        AssignmentRhs r = s.Rhss.First();
        AST.Expression rhs = TrAssignmentRhs(r);
        AST.AssignStatement ast = new AST.AssignStatement(lhs,rhs);
        return ast;  // TODO - multiple left and right sides

      } else if (stmt is AssignStmt) {
        Console.WriteLine("Not implemented: assign statement");
        return null;  // TODO

        // var s = (AssignStmt) stmt;
        // Contract.Assert(!(s.Lhs is SeqSelectExpr) ||
        //                 ((SeqSelectExpr) s.Lhs).SelectOne); // multi-element array assignments are not allowed
        // if (s.Rhs is HavocRhs) {
        //   if (DafnyOptions.O.ForbidNondeterminism) {
        //     Error(s.Rhs.Tok, "nondeterministic assignment forbidden by /definiteAssignment:3 option", wr);
        //   }
        // }
        // else {
        //   var lvalue = CreateLvalue(s.Lhs, wr);
        //   var wStmts = wr.ForkSection();
        //   var wRhs = EmitAssignment(lvalue, s.Lhs.Type, TypeOfRhs(s.Rhs), wr);
        //   TrRhs(s.Rhs, wRhs, wStmts);
        // }

      } else if (stmt is AssignSuchThatStmt) {
        Console.WriteLine("Not implemented: AssignSuchThat statement");
        return null;  // TODO
        // var s = (AssignSuchThatStmt) stmt;
        // if (DafnyOptions.O.ForbidNondeterminism) {
        //   Error(s.Tok, "assign-such-that statement forbidden by /definiteAssignment:3 option", wr);
        // }
        //
        // if (s.AssumeToken != null) {
        //   // Note, a non-ghost AssignSuchThatStmt may contain an assume
        //   Error(s.AssumeToken, "an assume statement cannot be compiled", wr);
        // }
        // else {
        //   var lhss = s.Lhss.ConvertAll(lhs =>
        //     ((IdentifierExpr) lhs.Resolved).Var); // the resolver allows only IdentifierExpr left-hand sides
        //   var missingBounds =
        //     ComprehensionExpr.BoundedPool.MissingBounds(lhss, s.Bounds,
        //       ComprehensionExpr.BoundedPool.PoolVirtues.Enumerable);
        //   if (missingBounds.Count != 0) {
        //     foreach (var bv in missingBounds) {
        //       Error(s.Tok,
        //         "this assign-such-that statement is too advanced for the current compiler; Dafny's heuristics cannot find any bound for variable '{0}'",
        //         wr, bv.Name);
        //     }
        //   }
        //   else {
        //     Contract.Assert(s.Bounds != null);
        //     TrAssignSuchThat(lhss, s.Expr, s.Bounds, s.Tok.line, wr, false);
        //   }
        // }

      } else if (stmt is AssignOrReturnStmt) {
        Console.WriteLine("Not implemented: AssignOrReturn statement");
        return null;  // TODO

        // var s = (AssignOrReturnStmt) stmt;
        // // TODO there's potential here to use target-language specific features such as exceptions
        // // to make it more target-language idiomatic and improve performance
        // TrStmtList(s.ResolvedStatements, wr);

      } else if (stmt is ExpectStmt) {
        Console.WriteLine("Not implemented: expect statement");
        return null;  // TODO

        // var s = (ExpectStmt) stmt;
        // // TODO there's potential here to use target-language specific features such as exceptions
        // // to make it more target-language idiomatic and improve performance
        // TargetWriter guardWriter;
        // TargetWriter bodyWriter = EmitIf(out guardWriter, false, wr);
        // var negated = new UnaryOpExpr(s.Tok, UnaryOpExpr.Opcode.Not, s.Expr);
        // negated.Type = Type.Bool;
        // TrExpr(negated, guardWriter, false);
        // EmitHalt(s.Message, bodyWriter);

      } else if (stmt is CallStmt) {
        Console.WriteLine("Not implemented: call statement");
        return null;  // TODO

        // var s = (CallStmt) stmt;
        // TrCallStmt(s, null, wr);

      } else if (stmt is BlockStmt) {
        AST.BlockStatement ast = new AST.BlockStatement();
        BlockStmt bl = (BlockStmt)stmt;
        foreach (Statement s in bl.Body) {
          AST.Statement st = TrStmt(s);
          if (st != null) ast.statements.Add(st);
        }
        return ast;
        
      } else if (stmt is IfStmt) {
        IfStmt s = (IfStmt) stmt;
        Console.WriteLine("Not implemented: if statement");
        return null;  // TODO

        // if (s.Guard == null) {
        //   if (DafnyOptions.O.ForbidNondeterminism) {
        //     Error(s.Tok, "nondeterministic if statement forbidden by /definiteAssignment:3 option", wr);
        //   }
        //
        //   // we can compile the branch of our choice
        //   if (s.Els == null) {
        //     // let's compile the "else" branch, since that involves no work
        //     // (still, let's leave a marker in the source code to indicate that this is what we did)
        //     Coverage.UnusedInstrumentationPoint(s.Thn.Tok, "then branch");
        //     wr = wr.NewBlock("if (!false) ");
        //     Coverage.Instrument(s.Tok, "implicit else branch", wr);
        //     wr.WriteLine("if (!false) { }");
        //   }
        //   else {
        //     // let's compile the "then" branch
        //     wr = wr.NewBlock("if (true) ");
        //     Coverage.Instrument(s.Thn.Tok, "then branch", wr);
        //     TrStmtList(s.Thn.Body, wr);
        //     Coverage.UnusedInstrumentationPoint(s.Els.Tok, "else branch");
        //   }
        // }
        // else {
        //   if (s.IsBindingGuard && DafnyOptions.O.ForbidNondeterminism) {
        //     Error(s.Tok, "binding if statement forbidden by /definiteAssignment:3 option", wr);
        //   }
        //
        //   TargetWriter guardWriter;
        //   var coverageForElse = Coverage.IsRecording && !(s.Els is IfStmt);
        //   var thenWriter = EmitIf(out guardWriter, s.Els != null || coverageForElse, wr);
        //   TrExpr(s.IsBindingGuard ? Translator.AlphaRename((ExistsExpr) s.Guard, "eg_d") : s.Guard, guardWriter, false);
        //
        //   // We'd like to do "TrStmt(s.Thn, indent)", except we want the scope of any existential variables to come inside the block
        //   if (s.IsBindingGuard) {
        //     IntroduceAndAssignBoundVars((ExistsExpr) s.Guard, thenWriter);
        //   }
        //
        //   Coverage.Instrument(s.Thn.Tok, "then branch", thenWriter);
        //   TrStmtList(s.Thn.Body, thenWriter);
        //
        //   if (coverageForElse) {
        //     wr = wr.NewBlock("", null, BlockTargetWriter.BraceStyle.Nothing);
        //     if (s.Els == null) {
        //       Coverage.Instrument(s.Tok, "implicit else branch", wr);
        //     }
        //     else {
        //       Coverage.Instrument(s.Els.Tok, "else branch", wr);
        //     }
        //   }
        //
        //   if (s.Els != null) {
        //     TrStmtNonempty(s.Els, wr);
        //   }
        // }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt) stmt;
        Console.WriteLine("// Not implemented: alternative statement");
        return null;  // TODO
        ///if (DafnyOptions.O.ForbidNondeterminism && 2 <= s.Alternatives.Count) {
        //  Error(s.Tok, "case-based if statement forbidden by /definiteAssignment:3 option", wr);
        //}

        // foreach (var alternative in s.Alternatives) {
        //   TargetWriter guardWriter;
        //   var thn = EmitIf(out guardWriter, true, wr);
        //   TrExpr(
        //     alternative.IsBindingGuard ? Translator.AlphaRename((ExistsExpr) alternative.Guard, "eg_d") : alternative.Guard,
        //     guardWriter, false);
        //   if (alternative.IsBindingGuard) {
        //     IntroduceAndAssignBoundVars((ExistsExpr) alternative.Guard, thn);
        //   }
        //
        //   Coverage.Instrument(alternative.Tok, "if-case branch", thn);
        //   TrStmtList(alternative.Body, thn);
        // }
        //
        // using (var wElse = wr.NewBlock("", null, BlockTargetWriter.BraceStyle.Nothing)) {
        //   EmitAbsurd("unreachable alternative", wElse);
        // }

      } else if (stmt is WhileStmt) {
        WhileStmt s = (WhileStmt) stmt;
        if (s.Body == null) {
          // this checks non-ghost body-less while statements
          Error(stmt.Tok, "a while statement without a body cannot be compiled", errorWr);
          return null;
        }

        return new AST.CommentStatement("Not implemented: while statement");  // TODO
        // if (s.Guard == null) {
        //   if (DafnyOptions.O.ForbidNondeterminism) {
        //     Error(s.Tok, "nondeterministic loop forbidden by /definiteAssignment:3 option", wr);
        //   }
        //
        //   // This loop is allowed to stop iterating at any time. We choose to never iterate, but we still
        //   // emit a loop structure. The structure "while (false) { }" comes to mind, but that results in
        //   // an "unreachable code" error from Java, so we instead use "while (true) { break; }".
        //   TargetWriter guardWriter;
        //   var wBody = CreateWhileLoop(out guardWriter, wr);
        //   guardWriter.Write("true");
        //   EmitBreak(s.Labels?.Data.AssignUniqueId(idGenerator), wBody);
        //   Coverage.UnusedInstrumentationPoint(s.Body.Tok, "while body");
        // }
        // else {
        //   var guardWriter = EmitWhile(s.Body.Tok, s.Body.Body, wr);
        //   TrExpr(s.Guard, guardWriter, false);
        // }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt) stmt;
        if (DafnyOptions.O.ForbidNondeterminism) {
          Error(s.Tok, "case-based loop forbidden by /definiteAssignment:3 option", errorWr);
        }
        Console.WriteLine("Not implemented: AlternativeLoop statement");
        return null;  // TODO

        // if (s.Alternatives.Count != 0) {
        //   TargetWriter whileGuardWriter;
        //   var w = CreateWhileLoop(out whileGuardWriter, wr);
        //   whileGuardWriter.Write("true");
        //   foreach (var alternative in s.Alternatives) {
        //     TargetWriter guardWriter;
        //     var thn = EmitIf(out guardWriter, true, w);
        //     TrExpr(alternative.Guard, guardWriter, false);
        //     Coverage.Instrument(alternative.Tok, "while-case branch", thn);
        //     TrStmtList(alternative.Body, thn);
        //   }
        //
        //   using (var wElse = w.NewBlock("")) {
        //     EmitBreak(null, wElse);
        //   }
        // }

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt) stmt;
        if (s.Kind != ForallStmt.BodyKind.Assign) {
          // Call and Proof have no side effects, so they can simply be optimized away.
          return null;
        }
        else if (s.BoundVars.Count == 0) {
          // the bound variables just spell out a single point, so the forall statement is equivalent to one execution of the body
          TrStmt(s.Body);
          return null;
        }
        Console.WriteLine("Not implemented: forall statement");
        return null;  // TODO

        // var s0 = (AssignStmt) s.S0;
        // if (s0.Rhs is HavocRhs) {
        //   if (DafnyOptions.O.ForbidNondeterminism) {
        //     Error(s0.Rhs.Tok, "nondeterministic assignment forbidden by /definiteAssignment:3 option", wr);
        //   }
        //
        //   // The forall statement says to havoc a bunch of things.  This can be efficiently compiled
        //   // into doing nothing.
        //   return;
        // }
        //
        // var rhs = ((ExprRhs) s0.Rhs).Expr;
        //
        // if (CanSequentializeForall(s.BoundVars, s.Bounds, s.Range, s0.Lhs, rhs)) {
        //   // Just put the statement inside the loops
        //   var wLoop = CompileGuardedLoops(s.BoundVars, s.Bounds, s.Range, wr);
        //   TrStmt(s0, wLoop);
        // }
        // else {
        //   // Compile:
        //   //   forall (w,x,y,z | Range(w,x,y,z)) {
        //   //     LHS(w,x,y,z) := RHS(w,x,y,z);
        //   //   }
        //   // where w,x,y,z have types seq<W>,set<X>,int,bool and LHS has L-1 top-level subexpressions
        //   // (that is, L denotes the number of top-level subexpressions of LHS plus 1),
        //   // into:
        //   //   var ingredients = new List< L-Tuple >();
        //   //   foreach (W w in sq.UniqueElements) {
        //   //     foreach (X x in st.Elements) {
        //   //       for (BigInteger y = Lo; j < Hi; j++) {
        //   //         for (bool z in Helper.AllBooleans) {
        //   //           if (Range(w,x,y,z)) {
        //   //             ingredients.Add(new L-Tuple( LHS0(w,x,y,z), LHS1(w,x,y,z), ..., RHS(w,x,y,z) ));
        //   //           }
        //   //         }
        //   //       }
        //   //     }
        //   //   }
        //   //   foreach (L-Tuple l in ingredients) {
        //   //     LHS[ l0, l1, l2, ..., l(L-2) ] = l(L-1);
        //   //   }
        //   //
        //   // Note, because the .NET Tuple class only supports up to 8 components, the compiler implementation
        //   // here supports arrays only up to 6 dimensions.  This does not seem like a serious practical limitation.
        //   // However, it may be more noticeable if the forall statement supported forall assignments in its
        //   // body.  To support cases where tuples would need more than 8 components, .NET Tuple's would have to
        //   // be nested.
        //
        //   // Temporary names
        //   var c = idGenerator.FreshNumericId("_ingredients+_tup");
        //   string ingredients = "_ingredients" + c;
        //   string tup = "_tup" + c;
        //
        //   // Compute L
        //   int L;
        //   string tupleTypeArgs;
        //   List<Type> tupleTypeArgsList;
        //   if (s0.Lhs is MemberSelectExpr) {
        //     var lhs = (MemberSelectExpr) s0.Lhs;
        //     L = 2;
        //     tupleTypeArgs = TypeArgumentName(lhs.Obj.Type, wr, lhs.tok);
        //     tupleTypeArgsList = new List<Type> {lhs.Obj.Type};
        //   }
        //   else if (s0.Lhs is SeqSelectExpr) {
        //     var lhs = (SeqSelectExpr) s0.Lhs;
        //     L = 3;
        //     // note, we might as well do the BigInteger-to-int cast for array indices here, before putting things into the Tuple rather than when they are extracted from the Tuple
        //     tupleTypeArgs = TypeArgumentName(lhs.Seq.Type, wr, lhs.tok) + IntSelect;
        //     tupleTypeArgsList = new List<Type> {lhs.Seq.Type, null};
        //   }
        //   else {
        //     var lhs = (MultiSelectExpr) s0.Lhs;
        //     L = 2 + lhs.Indices.Count;
        //     if (8 < L) {
        //       Error(lhs.tok,
        //         "compiler currently does not support assignments to more-than-6-dimensional arrays in forall statements",
        //         wr);
        //       return;
        //     }
        //
        //     tupleTypeArgs = TypeArgumentName(lhs.Array.Type, wr, lhs.tok);
        //     tupleTypeArgsList = new List<Type> {lhs.Array.Type};
        //     for (int i = 0; i < lhs.Indices.Count; i++) {
        //       // note, we might as well do the BigInteger-to-int cast for array indices here, before putting things into the Tuple rather than when they are extracted from the Tuple
        //       tupleTypeArgs += IntSelect;
        //       tupleTypeArgsList.Add(null);
        //     }
        //
        //   }
        //
        //   tupleTypeArgs += "," + TypeArgumentName(rhs.Type, wr, rhs.tok);
        //   tupleTypeArgsList.Add(rhs.Type);
        //
        //   // declare and construct "ingredients"
        //   var wrOuter = EmitIngredients(wr, ingredients, L, tupleTypeArgs, s, s0, rhs);
        //
        //   //   foreach (L-Tuple l in ingredients) {
        //   //     LHS[ l0, l1, l2, ..., l(L-2) ] = l(L-1);
        //   //   }
        //   TargetWriter collWriter;
        //   TargetTupleSize = L;
        //   wr = CreateForeachLoop(tup, null, out collWriter, wrOuter);
        //   collWriter.Write(ingredients);
        //   {
        //     var wTup = new TargetWriter(wr.IndentLevel, true);
        //     var wCoerceTup = EmitCoercionToArbitraryTuple(wTup);
        //     wCoerceTup.Write(tup);
        //     tup = wTup.ToString();
        //   }
        //   if (s0.Lhs is MemberSelectExpr) {
        //     EmitMemberSelect(s0, tupleTypeArgsList, wr, tup);
        //   }
        //   else if (s0.Lhs is SeqSelectExpr) {
        //     EmitSeqSelect(s0, tupleTypeArgsList, wr, tup);
        //   }
        //   else {
        //     EmitMultiSelect(s0, tupleTypeArgsList, wr, tup, L);
        //   }
        // }
      } else if (stmt is ConcreteSyntaxStatement) {
        var s = (ConcreteSyntaxStatement) stmt;
        Console.WriteLine("Not implemented: concrete syntax statement");
        return null;  // TODO

//        TrStmt(s.ResolvedStatement, wr);

      } else if (stmt is MatchStmt) {
        MatchStmt s = (MatchStmt) stmt;
        Console.WriteLine("Not implemented: match statement");
        return null;  // TODO
        // Type source = e;
        // if (source.is_Ctor0) {
        //   FormalType f0 = ((Dt_Ctor0)source._D).a0;
        //   ...
        //   Body0;
        // } else if (...) {
        //   ...
        // } else if (true) {
        //   ...
        // }
        // if (s.Cases.Count != 0) {
        //   string source = idGenerator.FreshId("_source");
        //   DeclareLocalVar(source, s.Source.Type, s.Source.tok, s.Source, false, wr);
        //
        //   int i = 0;
        //   var sourceType = (UserDefinedType) s.Source.Type.NormalizeExpand();
        //   foreach (MatchCaseStmt mc in s.Cases) {
        //     var w = MatchCasePrelude(source, sourceType, cce.NonNull(mc.Ctor), mc.Arguments, i, s.Cases.Count, wr);
        //     TrStmtList(mc.Body, w);
        //     i++;
        //   }
        // }

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt) stmt;
        LocalVariable v = s.Locals.First();
        AST.Type t = TrType(v.type); 
        AST.Expression init = null;
        IEnumerable<AssignmentRhs> exprs = ((UpdateStmt)s.Update).Rhss;
        if (exprs.Count() != 0) {
          init= TrAssignmentRhs(exprs.First());
        }
        return new AST.VarDeclaration(v.Name, t, init);
        Console.WriteLine("Not implemented: var decl statement");
        return null;  // TODO
        // var i = 0;
        // foreach (var local in s.Locals) {
        //   bool hasRhs = s.Update is AssignSuchThatStmt;
        //   if (!hasRhs && s.Update is UpdateStmt u) {
        //     if (i < u.Rhss.Count && u.Rhss[i] is HavocRhs) {
        //       // there's no specific initial value
        //     }
        //     else {
        //       hasRhs = true;
        //     }
        //   }
        //
        //   TrLocalVar(local, !hasRhs, wr);
        //   i++;
        // }
        //
        // if (s.Update != null) {
        //   TrStmt(s.Update, wr);
        // }

      } else if (stmt is LetStmt) {
        var s = (LetStmt) stmt;
        Console.WriteLine("Not implemented: let statement");
        return null;  // TODO
        // if (Contract.Exists(s.LHS.Vars, bv => !bv.IsGhost)) {
        //   TrCasePatternOpt(s.LHS, s.RHS, wr, false);
        // }
      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt) stmt;
        Console.WriteLine("Not implemented: modify statement");
        return null;  // TODO
        // if (s.Body != null) {
        //   TrStmt(s.Body, wr);
        // }
        // else if (DafnyOptions.O.ForbidNondeterminism) {
        //   Error(s.Tok, "modify statement without a body forbidden by /definiteAssignment:3 option", wr);
        // }

      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException(); // unexpected statement
      }
    }
    
    protected AST.Expression TrExpr(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Requires(errorWr != null); 
      if (expr is LiteralExpr) {
        LiteralExpr e = (LiteralExpr)expr;
        return new AST.Literal(e.Value.ToString());
        //EmitLiteralExpr(wr, e);

      } else if (expr is ThisExpr) {
        return new AST.Identifier("this");

      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        string n = e.Name;
        if (results != null) {
          n = results[n];
          if (n == null) n = e.Name;
        }
        return new AST.Identifier(n); // TODO

        // if (e.Var is Formal && inLetExprBody && !((Formal)e.Var).InParam) {
        //   // out param in letExpr body, need to copy it to a temp since
        //   // letExpr body is translated to an anonymous function that doesn't
        //   // allow out parameters
        //   var name = string.Format("_pat_let_tv{0}", GetUniqueAstNumber(e));
        //   wr.Write(name);
        //   DeclareLocalVar(name, null, null, false, IdName(e.Var), copyInstrWriters.Peek(), e.Type);
        // } else {
        //   wr.Write(IdName(e.Var));
        // }
      } else if (expr is SetDisplayExpr) {
        var e = (SetDisplayExpr)expr;
        return new AST.CommentExpr("SetDisplayExpr is not implemented"); // TODO
//        EmitCollectionDisplay(e.Type.AsSetType, e.tok, e.Elements, inLetExprBody, wr);

      } else if (expr is MultiSetDisplayExpr) {
        var e = (MultiSetDisplayExpr)expr;
        return new AST.CommentExpr("MultiSetDisplayExpr is not implemented"); // TODO
//        EmitCollectionDisplay(e.Type.AsMultiSetType, e.tok, e.Elements, inLetExprBody, wr);

      } else if (expr is SeqDisplayExpr) {
        var e = (SeqDisplayExpr)expr;
        return new AST.CommentExpr("SeqDisplayExpr is not implemented"); // TODO
        //EmitCollectionDisplay(e.Type.AsSeqType, e.tok, e.Elements, inLetExprBody, wr);

      } else if (expr is MapDisplayExpr) {
        var e = (MapDisplayExpr)expr;
        return new AST.CommentExpr("MapDisplayExpr is not implemented"); // TODO

//        EmitMapDisplay(e.Type.AsMapType, e.tok, e.Elements, inLetExprBody, wr);

      } else if (expr is MemberSelectExpr) {
        MemberSelectExpr e = (MemberSelectExpr)expr;
        //SpecialField sf = e.Member as SpecialField;
        return new AST.Select(TrExpr(e.Obj), e.MemberName); // TODO

        // if (sf != null) {
        //   string compiledName, preStr, postStr;
        //   GetSpecialFieldInfo(sf.SpecialId, sf.IdParam, out compiledName, out preStr, out postStr);
        //   wr.Write(preStr);
        //
        //   void writeObj(TargetWriter w) {
        //     if (NeedsCustomReceiver(e.Member) || sf.IsStatic) {
        //       w.Write(TypeName_Companion(e.Obj.Type, wr, e.tok, sf));
        //     } else {
        //       TrParenExpr(e.Obj, w, inLetExprBody);
        //     }
        //   }
        //
        //   EmitMemberSelect(writeObj, e.Member, expr.Type).EmitRead(wr);
        //
        //   if (NeedsCustomReceiver(e.Member)) {
        //     TrParenExpr(e.Obj, wr, inLetExprBody);
        //   }
        //
        //   wr.Write(postStr);
        // } else {
        //   EmitMemberSelect(w => TrExpr(e.Obj, w, inLetExprBody), e.Member, expr.Type).EmitRead(wr);
        // }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        Contract.Assert(e.Seq.Type != null);
        if (e.SelectOne) {
          return new AST.Index(TrExpr(e.Seq), TrExpr(e.E0));
        } else {
          return new AST.CommentExpr("Multi-SeqSelectExpr not implemented");
        }

        // if (e.Seq.Type.IsArrayType) {
        //   if (e.SelectOne) {
        //     Contract.Assert(e.E0 != null && e.E1 == null);
        //     var w = EmitArraySelect(new List<Expression>() { e.E0 }, e.Type, inLetExprBody, wr);
        //     TrParenExpr(e.Seq, w, inLetExprBody);
        //   } else {
        //     EmitSeqSelectRange(e.Seq, e.E0, e.E1, true, inLetExprBody, wr);
        //   }
        // } else if (e.SelectOne) {
        //   Contract.Assert(e.E0 != null && e.E1 == null);
        //   EmitIndexCollectionSelect(e.Seq, e.E0, inLetExprBody, wr);
        // } else {
        //   EmitSeqSelectRange(e.Seq, e.E0, e.E1, false, inLetExprBody, wr);
        // }
      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        return new AST.CommentExpr("SeqConstructionExpr is not implemented"); // TODO
        //EmitSeqConstructionExpr(e, inLetExprBody, wr);
      } else if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        return new AST.CommentExpr("MultiSetFormingExpr is not implemented"); // TODO
        //EmitMultiSetFormingExpr(e, inLetExprBody, wr);
      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;
        return new AST.CommentExpr("MultiSelectExpr is not implemented"); // TODO

        // WriteCast(TypeName(e.Type.NormalizeExpand(), wr, e.tok), wr);
        // var w = EmitArraySelect(e.Indices, e.Type, inLetExprBody, wr);
        // TrParenExpr(e.Array, w, inLetExprBody);

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        return new AST.CommentExpr("SeqUpdateExpr is not implemented"); // TODO
        // if (e.ResolvedUpdateExpr != null) {
        //   TrExpr(e.ResolvedUpdateExpr, wr, inLetExprBody);
        // } else {
        //   EmitIndexCollectionUpdate(e.Seq, e.Index, e.Value, inLetExprBody, wr);
        // }

      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        return new AST.Apply(new AST.Identifier(e.Name), TrArgs(e.Args));
        return new AST.CommentExpr("FunctionCallExpr is not implemented"); // TODO

        // if (e.Function is SpecialFunction) {
        //   CompileSpecialFunctionCallExpr(e, wr, inLetExprBody, TrExpr);
        // } else {
        //   CompileFunctionCallExpr(e, wr, inLetExprBody, TrExpr);
        // }

      } else if (expr is ApplyExpr) {
        var e = expr as ApplyExpr;
        return new AST.CommentExpr("ApplyExpr is not implemented"); // TODO
        //EmitApplyExpr(e.Function.Type, e.tok, e.Function, e.Args, inLetExprBody, wr);

      } else if (expr is DatatypeValue) {
        var dtv = (DatatypeValue)expr;
        return new AST.CommentExpr("DatatypeValue is not implemented"); // TODO

        // Contract.Assert(dtv.Ctor != null);  // since dtv has been successfully resolved
        //
        // var wrArgumentList = new TargetWriter();
        // string sep = "";
        // for (int i = 0; i < dtv.Arguments.Count; i++) {
        //   var formal = dtv.Ctor.Formals[i];
        //   if (!formal.IsGhost) {
        //     wrArgumentList.Write(sep);
        //     var w = EmitCoercionIfNecessary(from:dtv.Arguments[i].Type, to:dtv.Ctor.Formals[i].Type, tok:dtv.tok, wr:wrArgumentList);
        //     TrExpr(dtv.Arguments[i], w, inLetExprBody);
        //     sep = ", ";
        //   }
        // }
        // EmitDatatypeValue(dtv, wrArgumentList.ToString(), wr);

      } else if (expr is OldExpr) {
        return new AST.Apply(new AST.Identifier("\\old"), arglist(TrExpr(((OldExpr)expr).E)));
        Contract.Assert(false); throw new cce.UnreachableException();  // 'old' is always a ghost
        return new AST.CommentExpr("OldExpr is not implemented"); // TODO

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        AST.Expression arg = TrExpr(e.E);
        AST.Expression ast = null;
        switch (e.Op) {
          case UnaryOpExpr.Opcode.Not:
            if (e.Type.IsBitVectorType) {
              //var bvType = e.Type.AsBitVectorType;
              //var wrTruncOperand = EmitBitvectorTruncation(bvType, false, wr);
              ast = new AST.Unary("~", arg);
            } else {
              ast = new AST.Unary("!", arg);
            }
            break;
          case UnaryOpExpr.Opcode.Cardinality:
            return new AST.CommentExpr("UnaryOpExpr-Cardinality is not implemented"); // TODO
            break;
          case UnaryOpExpr.Opcode.Fresh: 
            ast = new AST.Apply(new AST.Identifier("\\fresh"), arglist(arg));
            break;
          default:
            ast = new AST.CommentExpr("UnaryOpExpr is not implemented"); // TODO
            break;
            //Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary expression
        }
        return ast;

      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        return new AST.CommentExpr("ConversionExpr is not implemented"); // TODO
        //EmitConversionExpr(e, inLetExprBody, wr);

      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        AST.Expression lhs = TrExpr(e.E0);
        AST.Expression rhs = TrExpr(e.E1);
        string op = null;
        switch (e.Op) {
          case BinaryExpr.Opcode.Eq: op = "="; break;
          case BinaryExpr.Opcode.Gt: op = ">"; break;
          case BinaryExpr.Opcode.Lt: op = "<"; break;
          case BinaryExpr.Opcode.Ge: op = ">="; break;
          case BinaryExpr.Opcode.Le: op = "<="; break;
          case BinaryExpr.Opcode.Neq: op = "!="; break;
          case BinaryExpr.Opcode.Add: op = "+"; break;
          case BinaryExpr.Opcode.Sub: op = "-"; break;
          case BinaryExpr.Opcode.Mul: op = "*"; break;
          case BinaryExpr.Opcode.Div: op = "/"; break; // TODO
          case BinaryExpr.Opcode.Mod: op = "%"; break; // TODO
          case BinaryExpr.Opcode.And: op = "&&"; break;
          case BinaryExpr.Opcode.Or: op = "||"; break;
          case BinaryExpr.Opcode.Imp: op = "==>"; break;
          case BinaryExpr.Opcode.Iff: op = "<==>"; break;
          case BinaryExpr.Opcode.BitwiseAnd: op = "&"; break;
          case BinaryExpr.Opcode.BitwiseOr: op = "|"; break;
          case BinaryExpr.Opcode.BitwiseXor: op = "^"; break;
          case BinaryExpr.Opcode.RightShift: op = "<<"; break;
          case BinaryExpr.Opcode.LeftShift: op = ">>"; break;
          // TODO: Disjoint, In, NotIn, Exp,
          default: break; // TODO - more cases; need to check that precedence is the same
        }

        if (op == null) return new AST.CommentExpr("BinaryExpr is not implemented for given op"); // TODO
        else return new AST.Binary(lhs, op, rhs);
        // if (IsComparisonToZero(e, out var arg, out var sign, out var negated) &&
        //     CompareZeroUsingSign(arg.Type)) {
        //   // Transform e.g. x < BigInteger.Zero into x.Sign == -1
        //   var w = EmitSign(arg.Type, wr);
        //   TrParenExpr(arg, w, inLetExprBody);
        //   wr.Write(negated ? " != " : " == ");
        //   wr.Write(sign);
        // } else {
        //   string opString, preOpString, postOpString, callString, staticCallString;
        //   bool reverseArguments, truncateResult, convertE1_to_int;
        //   CompileBinOp(e.ResolvedOp, e.E0, e.E1, e.tok, expr.Type,
        //     out opString,
        //     out preOpString,
        //     out postOpString,
        //     out callString,
        //     out staticCallString,
        //     out reverseArguments,
        //     out truncateResult,
        //     out convertE1_to_int,
        //     wr);
        //
        //   if (truncateResult && e.Type.IsBitVectorType) {
        //     wr = EmitBitvectorTruncation(e.Type.AsBitVectorType, true, wr);
        //   }
        //   var e0 = reverseArguments ? e.E1 : e.E0;
        //   var e1 = reverseArguments ? e.E0 : e.E1;
        //   if (opString != null) {
        //     var nativeType = AsNativeType(e.Type);
        //     string nativeName = null, literalSuffix = null;
        //     bool needsCast = false;
        //     if (nativeType != null) {
        //       GetNativeInfo(nativeType.Sel, out nativeName, out literalSuffix, out needsCast);
        //     }
        //     if (needsCast) {
        //       wr.Write("(" + nativeName + ")(");
        //     }
        //     wr.Write(preOpString);
        //     TrParenExpr(e0, wr, inLetExprBody);
        //     wr.Write(" {0} ", opString);
        //     if (convertE1_to_int) {
        //       EmitExprAsInt(e1, inLetExprBody, wr);
        //     } else {
        //       TrParenExpr(e1, wr, inLetExprBody);
        //     }
        //     if (needsCast) {
        //       wr.Write(")");
        //     }
        //     wr.Write(postOpString);
        //   } else if (callString != null) {
        //     wr.Write(preOpString);
        //     TrParenExpr(e0, wr, inLetExprBody);
        //     wr.Write(".{0}(", callString);
        //     if (convertE1_to_int) {
        //       EmitExprAsInt(e1, inLetExprBody, wr);
        //     } else {
        //       TrParenExpr(e1, wr, inLetExprBody);
        //     }
        //     wr.Write(")");
        //     wr.Write(postOpString);
        //   } else if (staticCallString != null) {
        //     wr.Write(preOpString);
        //     wr.Write("{0}(", staticCallString);
        //     TrExpr(e0, wr, inLetExprBody);
        //     wr.Write(", ");
        //     TrExpr(e1, wr, inLetExprBody);
        //     wr.Write(")");
        //     wr.Write(postOpString);
        //   }
        // }
      } else if (expr is TernaryExpr) {
        Contract.Assume(false);  // currently, none of the ternary expressions is compilable
        return new AST.CommentExpr("TernaryExpr is not implemented"); // TODO

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        return new AST.CommentExpr("LetExpr is not implemented"); // TODO

        // if (e.Exact) {
        //   // The Dafny "let" expression
        //   //    var Pattern(x,y) := G; E
        //   // is translated into C# as:
        //   //    LamLet(G, tmp =>
        //   //      LamLet(dtorX(tmp), x =>
        //   //      LamLet(dtorY(tmp), y => E)))
        //   Contract.Assert(e.LHSs.Count == e.RHSs.Count);  // checked by resolution
        //   var w = wr;
        //   for (int i = 0; i < e.LHSs.Count; i++) {
        //     var lhs = e.LHSs[i];
        //     if (Contract.Exists(lhs.Vars, bv => !bv.IsGhost)) {
        //       var rhsName = string.Format("_pat_let{0}_{1}", GetUniqueAstNumber(e), i);
        //       w = CreateIIFE_ExprBody(e.RHSs[i], inLetExprBody, e.RHSs[i].Type, e.RHSs[i].tok, e.Body.Type, e.Body.tok, rhsName, w);
        //       w = TrCasePattern(lhs, rhsName, e.Body.Type, w);
        //     }
        //   }
        //   TrExpr(e.Body, w, true);
        // } else if (e.BoundVars.All(bv => bv.IsGhost)) {
        //   // The Dafny "let" expression
        //   //    ghost var x,y :| Constraint; E
        //   // is compiled just like E is, because the resolver has already checked that x,y (or other ghost variables, for that matter) don't
        //   // occur in E (moreover, the verifier has checked that values for x,y satisfying Constraint exist).
        //   TrExpr(e.Body, wr, inLetExprBody);
        // } else {
        //   // The Dafny "let" expression
        //   //    var x,y :| Constraint; E
        //   // is translated into C# as:
        //   //    LamLet(0, dummy => {  // the only purpose of this construction here is to allow us to add some code inside an expression in C#
        //   //        var x,y;
        //   //        // Embark on computation that fills in x,y according to Constraint; the computation stops when the first
        //   //        // such value is found, but since the verifier checks that x,y follows uniquely from Constraint, this is
        //   //        // not a source of nondeterminancy.
        //   //        return E;
        //   //      })
        //   Contract.Assert(e.RHSs.Count == 1);  // checked by resolution
        //   var missingBounds = ComprehensionExpr.BoolBoundedPool.MissingBounds(e.BoundVars.ToList<BoundVar>(), e.Constraint_Bounds, ComprehensionExpr.BoundedPool.PoolVirtues.Enumerable);
        //   if (missingBounds.Count != 0) {
        //     foreach (var bv in missingBounds) {
        //       Error(e.tok, "this let-such-that expression is too advanced for the current compiler; Dafny's heuristics cannot find any bound for variable '{0}'", wr, bv.Name);
        //     }
        //   } else {
        //     var w = CreateIIFE1(0, e.Body.Type, e.Body.tok, "_let_dummy_" + GetUniqueAstNumber(e), wr);
        //     foreach (var bv in e.BoundVars) {
        //       DeclareLocalVar(IdName(bv), bv.Type, bv.tok, false, DefaultValue(bv.Type, wr, bv.tok), w);
        //     }
        //     TrAssignSuchThat(new List<IVariable>(e.BoundVars).ConvertAll(bv => (IVariable)bv), e.RHSs[0], e.Constraint_Bounds, e.tok.line, w, inLetExprBody);
        //     EmitReturnExpr(e.Body, true, w);
        //   }
        // }
      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        return new AST.CommentExpr("MatchExpr is not implemented"); // TODO

        // // ((System.Func<SourceType, TargetType>)((SourceType _source) => {
        // //   if (source.is_Ctor0) {
        // //     FormalType f0 = ((Dt_Ctor0)source._D).a0;
        // //     ...
        // //     return Body0;
        // //   } else if (...) {
        // //     ...
        // //   } else if (true) {
        // //     ...
        // //   }
        // // }))(src)
        //
        // string source = idGenerator.FreshId("_source");
        // var w = CreateLambda(new List<Type>() { e.Source.Type }, e.tok, new List<string>() { source }, e.Type, wr);
        //
        // if (e.Cases.Count == 0) {
        //   // the verifier would have proved we never get here; still, we need some code that will compile
        //   EmitAbsurd(null, w);
        // } else {
        //   int i = 0;
        //   var sourceType = (UserDefinedType)e.Source.Type.NormalizeExpand();
        //   foreach (MatchCaseExpr mc in e.Cases) {
        //     var wCase = MatchCasePrelude(source, sourceType, mc.Ctor, mc.Arguments, i, e.Cases.Count, w);
        //     EmitReturnExpr(mc.Body, inLetExprBody, wCase);
        //     i++;
        //   }
        // }
        // // We end with applying the source expression to the delegate we just built
        // wr.Write(LambdaExecute);
        // TrParenExpr(e.Source, wr, inLetExprBody);

      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        return new AST.CommentExpr("QuantifierExpr is not implemented"); // TODO

        // Compilation does not check whether a quantifier was split.

        // Contract.Assert(e.Bounds != null);  // for non-ghost quantifiers, the resolver would have insisted on finding bounds
        // var n = e.BoundVars.Count;
        // Contract.Assert(e.Bounds.Count == n);
        // var wBody = wr;
        // for (int i = 0; i < n; i++) {
        //   var bound = e.Bounds[i];
        //   var bv = e.BoundVars[i];
        //   // emit:  Dafny.Helpers.Quantifier(rangeOfValues, isForall, bv => body)
        //   wBody.Write("{0}(", GetQuantifierName(TypeName(bv.Type, wBody, bv.tok)));
        //   CompileCollection(bound, bv, inLetExprBody, false, wBody, e.Bounds, e.BoundVars, i);
        //   wBody.Write(", {0}, ", expr is ForallExpr ? "true" : "false");
        //   var native = AsNativeType(e.BoundVars[i].Type);
        //   TargetWriter newWBody = CreateLambda(new List<Type>{ bv.Type }, e.tok, new List<string>{ IdName(bv) }, Type.Bool, wBody, untyped: true);
        //   newWBody = EmitReturnExpr(newWBody);
        //   wBody.Write(')');
        //   wBody = newWBody;
        // }
        // TrExpr(e.LogicalBody(true), wBody, true);

      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        return new AST.CommentExpr("SetComprehension is not implemented"); // TODO

        // // For "set i,j,k,l | R(i,j,k,l) :: Term(i,j,k,l)" where the term has type "G", emit something like:
        // // ((System.Func<Set<G>>)(() => {
        // //   var _coll = new List<G>();
        // //   foreach (var tmp_l in sq.Elements) { L l = (L)tmp_l;
        // //     foreach (var tmp_k in st.Elements) { K k = (K)tmp_k;
        // //       for (BigInteger j = Lo; j < Hi; j++) {
        // //         for (bool i in Helper.AllBooleans) {
        // //           if (R(i,j,k,l)) {
        // //             _coll.Add(Term(i,j,k,l));
        // //           }
        // //         }
        // //       }
        // //     }
        // //   }
        // //   return Dafny.Set<G>.FromCollection(_coll);
        // // }))()
        // Contract.Assert(e.Bounds != null);  // the resolver would have insisted on finding bounds
        // var typeName = TypeName(e.Type.AsSetType.Arg, wr, e.tok);
        // var collection_name = idGenerator.FreshId("_coll");
        // var bwr = CreateIIFE0(e.Type.AsSetType, e.tok, wr);
        // wr = bwr;
        // EmitSetComprehension(wr, expr, collection_name);
        // var n = e.BoundVars.Count;
        // Contract.Assert(e.Bounds.Count == n);
        // for (int i = 0; i < n; i++) {
        //   var bound = e.Bounds[i];
        //   var bv = e.BoundVars[i];
        //   TargetWriter collectionWriter;
        //   var tmpVar = idGenerator.FreshId("_compr_");
        //   wr = CreateForeachLoop(tmpVar, bv.Type, out collectionWriter, wr, IdName(bv), bv.Type, bv.tok);
        //   CompileCollection(bound, bv, inLetExprBody, true, collectionWriter);
        // }
        // TargetWriter guardWriter;
        // var thn = EmitIf(out guardWriter, false, wr);
        // TrExpr(e.Range, guardWriter, inLetExprBody);
        // EmitCollectionBuilder_Add(e.Type.AsSetType, collection_name, e.Term, inLetExprBody, thn);
        // var s = GetCollectionBuilder_Build(e.Type.AsSetType, e.tok, collection_name, wr);
        // EmitReturnExpr(s, bwr);

      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        return new AST.CommentExpr("MapComprehension is not implemented"); // TODO

        // // For "map i | R(i) :: Term(i)" where the term has type "V" and i has type "U", emit something like:
        // // ((System.Func<Map<U, V>>)(() => {
        // //   var _coll = new List<Pair<U,V>>();
        // //   foreach (L l in sq.Elements) {
        // //     foreach (K k in st.Elements) {
        // //       for (BigInteger j = Lo; j < Hi; j++) {
        // //         for (bool i in Helper.AllBooleans) {
        // //           if (R(i,j,k,l)) {
        // //             _coll.Add(new Pair(i, Term(i));
        // //           }
        // //         }
        // //       }
        // //     }
        // //   }
        // //   return Dafny.Map<U, V>.FromCollection(_coll);
        // // }))()
        // Contract.Assert(e.Bounds != null);  // the resolver would have insisted on finding bounds
        // var domtypeName = TypeName(e.Type.AsMapType.Domain, wr, e.tok);
        // var rantypeName = TypeName(e.Type.AsMapType.Range, wr, e.tok);
        // var collection_name = idGenerator.FreshId("_coll");
        // wr = CreateIIFE0(e.Type.AsMapType, e.tok, wr);
        // using (var wrVarInit = DeclareLocalVar(collection_name, null, null, wr, e.Type.AsMapType)){
        //   EmitCollectionBuilder_New(e.Type.AsMapType, e.tok, wrVarInit);
        // }
        // var n = e.BoundVars.Count;
        // Contract.Assert(e.Bounds.Count == n && n == 1);
        // var bound = e.Bounds[0];
        // var bv = e.BoundVars[0];
        // Contract.Assume(e.BoundVars.Count == 1);  // TODO: implement the case where e.BoundVars.Count > 1
        // TargetWriter collectionWriter;
        // var w = CreateForeachLoop(IdName(bv), bv.Type, out collectionWriter, wr);
        // CompileCollection(bound, bv, inLetExprBody, true, collectionWriter);
        // TargetWriter guardWriter;
        // var thn = EmitIf(out guardWriter, false, w);
        // TrExpr(e.Range, guardWriter, inLetExprBody);
        // var termLeftWriter = EmitMapBuilder_Add(e.Type.AsMapType, e.tok, collection_name, e.Term, inLetExprBody, thn);
        // if (e.TermLeft == null) {
        //   termLeftWriter.Write(IdName(bv));
        // } else {
        //   TrExpr(e.TermLeft, termLeftWriter, inLetExprBody);
        // }
        //
        // var s = GetCollectionBuilder_Build(e.Type.AsMapType, e.tok, collection_name, wr);
        // EmitReturnExpr(s, wr);

      } else if (expr is LambdaExpr) {
        LambdaExpr e = (LambdaExpr)expr;
        return new AST.CommentExpr("LambdaExpr is not implemented"); // TODO

        //
        // List<BoundVar> bvars;
        // List<Expression> fexprs;
        // Translator.Substituter su;
        // CreateFreeVarSubstitution(expr, out bvars, out fexprs, out su);
        //
        // var typeArgs = TypeName_UDT(ArrowType.Arrow_FullCompileName, Util.Snoc(bvars.ConvertAll(bv => bv.Type), expr.Type), wr, Bpl.Token.NoToken);
        // var boundVars = Util.Comma(bvars, IdName);
        // wr = EmitBetaRedex(bvars.ConvertAll(IdName), fexprs, typeArgs, bvars.ConvertAll(bv => bv.Type), expr.Type, expr.tok, inLetExprBody, wr);
        // wr = CreateLambda(e.BoundVars.ConvertAll(bv => bv.Type), Bpl.Token.NoToken, e.BoundVars.ConvertAll(IdName), e.Body.Type, wr);
        // wr = EmitReturnExpr(wr);
        // TrExpr(su.Substitute(e.Body), wr, inLetExprBody);

      } else if (expr is StmtExpr) {
        return new AST.CommentExpr("StmtExpr is not implemented"); // TODO
        //var e = (StmtExpr)expr;
        //TrExpr(e.E, wr, inLetExprBody);

      } else if (expr is ITEExpr) {
        return new AST.CommentExpr("ITEExpr is not implemented"); // TODO
        // var e = (ITEExpr)expr;
        // EmitITE(e.Test, e.Thn, e.Els, inLetExprBody, wr);

    } else if (expr is NameSegment) {
        var e = (NameSegment) expr;
        string n = e.Name;
        if (results != null) { // TODO: Should only do lookup on simple variables
          n = results[n];
          if (n == null) n = e.Name;
        }
        return new AST.Identifier(n);
        
      } else if (expr is ApplySuffix) {
        var e = (ApplySuffix) expr;
        return new AST.Apply(TrExpr(e.Lhs), TrArgs(e.Args));

      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        String suffix = e.SuffixName;
        if (suffix == "Length") suffix = "length";
        AST.Expression arg = TrExpr(e.Lhs);
        return new AST.Suffix(arg, suffix);
        
      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        //TrExpr(e.ResolvedExpression, wr, inLetExprBody);
        return new AST.CommentExpr("ConcreteSyntaxExpr is not implemented"); // TODO

      } else if (expr is NamedExpr) {
        return new AST.CommentExpr("NamedExpr is not implemented"); // TODO
        //TrExpr(((NamedExpr)expr).Body, wr, inLetExprBody);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    public AST.Type TrType(Type t) {
      if (t is InferredTypeProxy) {
        t = ((InferredTypeProxy) t).T;
      }
      

      if (t is UserDefinedType) {
        UserDefinedType ut = (UserDefinedType) t;

        if (ut.IsArrayType) {
          Type tp = ut.TypeArgs.First();
          return new AST.ArrayType(TrType(tp), 1);
        } 
      } else {
        return new AST.SimpleType("int");
      }

      return new AST.SimpleType("**UnknownType**");
    }
    
    public AST.Expression TrAssignmentRhs(AssignmentRhs r) {
      if (r is ExprRhs) {
        ExprRhs erhs = (ExprRhs) r;
        return TrExpr(erhs.Expr);
      } else if (r is TypeRhs) {
        TypeRhs tr = (TypeRhs)r;
        Expression f = tr.ArrayDimensions.First();
        AST.Expression e = new AST.NewArray(TrType(tr.EType), TrExpr(f));
        return e;
      } else {
        AST.Expression e = new AST.CommentExpr("Not implemented kind of AssignmentRhs");
        return e;
      }

    }

    List<AST.Expression> TrArgs(List<Expression> args) {
      List<AST.Expression> list = new List<AST.Expression>();
      foreach (Expression ex in args) {
        list.Add(TrExpr(ex));
      }
      return list;
    }

    List<AST.Expression> arglist(params AST.Expression[] e) {
      return new List<AST.Expression>(e);
    }

  }

}