/*
    Definition of Haskell's abstract syntax in K, as based off of Language.Haskell.Exts.Syntax
*/

load ../../../../k-prelude
load hsStructs

kmod HASKELL-SYNTAX is
    including HASKELL-SYNTAX-STRUCTS
    including PL-STRING
    including K

    syntax K ::= Boxed
               | ModuleName
               | SpecialCon
               | QName
               | Name
               | IPName
               | QOp
               | Op
               | CName
               | Module
               | ExportSpec
               | ImportDecl
               | ImportSpec
               | Assoc
               | Decl
               | Annotation
               | DataOrNew
               | Binds
               | IPBind
               | Match
               | QualConDecl
               | ConDecl
               | GadtDecl
               | ClassDecl
               | InstDecl
               | BangType
               | Rhs
               | GuardedRhs
               | Type
               | TyVarBind
               | Kind
               | FunDep
               | Asst
               | Literal
               | Exp
               | XName
               | XAttr
               | Bracket
               | Splice
               | Safety
               | CallConv
               | ModulePragma
               | Activation
               | Rule
               | RuleVar
               | WarningText
               | Pat
               | PXAttr
               | RPatOp
               | RPat
               | PatField
               | Stmt
               | QualStmt
               | FieldUpdate
               | Alt
               | GuardedAlts
               | GuardedAlt
               | Syntax
               | Int
               | String
               | Bool
               | HsRational

    --- I'll flesh this out later
    sort HsRational

/*
    data Boxed = Boxed | Unboxed
*/
    --- Sort present in annotated Haskell syntax
    syntax Boxed ::= `Boxed
                   | `Unboxed


/*
data SrcLoc = SrcLoc
    { srcFilename :: String
    , srcLine :: Int
    , srcColumn :: Int
    }
*/
    --- Sort present in SrcLoc
    syntax SrcLoc ::= `SrcLoc K K K

/*
    -- | The name of a Haskell module.
    newtype ModuleName = ModuleName String
*/

    syntax ModuleName ::= `ModuleName K

/*
    -- | Constructors with special syntax.
    -- These names are never qualified, and always refer to builtin type or
    -- data constructors.
    data SpecialCon
        = UnitCon               -- ^ unit type and data constructor @()@
        | ListCon               -- ^ list type constructor @[]@
        | FunCon                -- ^ function type constructor @->@
        | TupleCon Boxed Int    -- ^ /n/-ary tuple type and data
                                --   constructors @(,)@ etc, possibly boxed @(\#,\#)@
        | Cons                  -- ^ list data constructor @(:)@
        | UnboxedSingleCon      -- ^ unboxed singleton tuple constructor @(\# \#)@
*/

    syntax SpecialCon ::= `UnitCon
                        | `ListCon
                        | `FunCon
                        | `TupleCon K K
                        | `Cons
                        | `UnboxedSingleCon

/*
    -- | This type is used to represent qualified variables, and also
    --   qualified constructors.
    data QName
        = Qual ModuleName Name    -- ^ name qualified with a module name
        | UnQual Name             -- ^ unqualified local name
        | Special SpecialCon      -- ^ built-in constructor with special syntax
*/

    syntax QName ::= `Qual  K K
                   | `UnQual K
                   | `Special K

/*
    -- | This type is used to represent variables, and also constructors.
    data Name
        = Ident String    -- ^ /varid/ or /conid/.
        | Symbol String   -- ^ /varsym/ or /consym/
*/

    syntax Name ::= `Ident K
                  | `Symbol K

/*
    -- | An implicit parameter name.
    data IPName
        = IPDup String -- ^ ?/ident/, non-linear implicit parameter
        | IPLin String -- ^ %/ident/, linear implicit parameter
*/

    syntax IPName ::= `IPDup K
                    | `IPLin K


/*
    -- | Possibly qualified infix operators (/qop/), appearing in expressions.
    data QOp
        = QVarOp QName  -- ^ variable operator (/qvarop/)
        | QConOp QName  -- ^ constructor operator (/canopy/)
*/

    syntax QOp ::= `QVarOp K
                 | `QConOp K

/*
    -- | Operators appearing in @infix@ declarations are never qualified.
    data Op
        = VarOp Name    -- ^ variable operator (/varop/)
        | ConOp Name    -- ^ constructor operator (/conop/)
*/

    syntax Op ::= `VarOp K
                | `ConOp K

/*
    -- | A name (/cname/) of a component of a class or data type in an @import@
    --   or export specification.
    data CName
        = VarName Name  -- ^ name of a method or field
        | ConName Name  -- ^ name of a data constructor
*/

    syntax CName ::= `VarName K
                   | `ConName K

/*
    -- | A complete Haskell source module.
    data Module = Module SrcLoc ModuleName [ModulePragma] (Maybe WarningText)
                            (Maybe [ExportSpec]) [ImportDecl] [Decl]
*/

    syntax Module ::= `Module K K K K K K K

/*
    -- | An item in a module's export specification.
    data ExportSpec
         = EVar QName                   -- ^ variable
         | EAbs QName                   -- ^ @T@:
                                        --   a class or datatype exported abstractly,
                                        --   or a type synonym.
         | EThingAll QName              -- ^ @T(..)@:
                                        --   a class exported with all of its methods, or
                                        --   a datatype exported with all of its constructors.
         | EThingWith QName [CName]     -- ^ @T(C_1,...,C_n)@:
                                        --   a class exported with some of its methods, or
                                        --   a datatype exported with some of its constructors.
         | EModuleContents ModuleName   -- ^ @module M@:
                                        --   re-export a module.
*/

    syntax ExportSpec ::= `EVar K
                        | `EAbs K
                        | `EThingAll K
                        | `EThingWith K K
                        | `EModuleContents K

/*
    -- | An import declaration.
    data ImportDecl = ImportDecl
        { importLoc :: SrcLoc           -- ^ position of the @import@ keyword.
        , importModule :: ModuleName    -- ^ name of the module imported.
        , importQualified :: Bool       -- ^ imported @qualified@?
        , importSrc :: Bool             -- ^ imported with @{-\# SOURCE \#-}@?
        , importPkg :: Maybe String     -- ^ imported with explicit package name
        , importAs :: Maybe ModuleName  -- ^ optional alias name in an @as@ clause.
        , importSpecs :: Maybe (Bool,[ImportSpec])
                -- ^ optional list of import specifications.
                -- The 'Bool' is 'True' if the names are excluded
                -- by @hiding@.
        }
*/

    syntax ImportDecl ::= `ImportDecl K K K K K K K

/*
    -- | An import specification, representing a single explicit item imported
    --   (or hidden) from a module.
    data ImportSpec
         = IVar Name                -- ^ variable
         | IAbs Name                -- ^ @T@:
                                    --   the name of a class, datatype or type synonym.
         | IThingAll Name           -- ^ @T(..)@:
                                    --   a class imported with all of its methods, or
                                    --   a datatype imported with all of its constructors.
         | IThingWith Name [CName]  -- ^ @T(C_1,...,C_n)@:
                                    --   a class imported with some of its methods, or
                                    --   a datatype imported with some of its constructors.
*/

    syntax ImportSpec ::= `IVar K
                        | `IAbs K
                        | `IThingAll K
                        | `IThingWith K K

/*
    -- | Associativity of an operator.
    data Assoc
         = AssocNone  -- ^ non-associative operator (declared with @infix@)
         | AssocLeft  -- ^ left-associative operator (declared with @infixl@).
         | AssocRight -- ^ right-associative operator (declared with @infixr@)
*/

    syntax Assoc ::= `AssocNone
                   | `AssocLeft
                   | `AssocRight

/*
    -- | A single derived instance, which may have arguments since it may be a MPTC.
    type Deriving = (QName, [Type])

    note: erasing type synonyms
*/


/*
    -- | A top-level declaration.
    data Decl
         = TypeDecl     SrcLoc Name [TyVarBind] Type
         -- ^ A type declaration
         | TypeFamDecl  SrcLoc Name [TyVarBind] (Maybe Kind)
         -- ^ A type family declaration
         | DataDecl     SrcLoc DataOrNew Context Name [TyVarBind]              [QualConDecl] [Deriving]
         -- ^ A data OR newtype declaration
         | GDataDecl    SrcLoc DataOrNew Context Name [TyVarBind] (Maybe Kind) [GadtDecl]    [Deriving]
         -- ^ A data OR newtype declaration, GADT style
         | DataFamDecl  SrcLoc {-data-}  Context Name [TyVarBind] (Maybe Kind)
         -- ^ A data family declaration
         | TypeInsDecl  SrcLoc Type Type
         -- ^ A type family instance declaration
         | DataInsDecl  SrcLoc DataOrNew Type              [QualConDecl] [Deriving]
         -- ^ A data family instance declaration
         | GDataInsDecl SrcLoc DataOrNew Type (Maybe Kind) [GadtDecl]    [Deriving]
         -- ^ A data family instance declaration, GADT style
         | ClassDecl    SrcLoc Context Name [TyVarBind] [FunDep] [ClassDecl]
         -- ^ A declaration of a type class
         | InstDecl     SrcLoc Context QName [Type] [InstDecl]
         -- ^ An declaration of a type class instance
         | DerivDecl    SrcLoc Context QName [Type]
         -- ^ A standalone deriving declaration
         | InfixDecl    SrcLoc Assoc Int [Op]
         -- ^ A declaration of operator fixity
         | DefaultDecl  SrcLoc [Type]
         -- ^ A declaration of default types
         | SpliceDecl   SrcLoc Exp
         -- ^ A Template Haskell splicing declaration
         | TypeSig      SrcLoc [Name] Type
         -- ^ A type signature declaration
         | FunBind      [Match]
         -- ^ A set of function binding clauses
         | PatBind      SrcLoc Pat (Maybe Type) Rhs {-where-} Binds
         -- ^ A pattern binding
         | ForImp   SrcLoc CallConv Safety String Name Type
         -- ^ A foreign import declaration
         | ForExp   SrcLoc CallConv          String Name Type
         -- ^ A foreign export declaration

         | RulePragmaDecl   SrcLoc [Rule]
         -- ^ A RULES pragma
         | DeprPragmaDecl   SrcLoc [([Name], String)]
         -- ^ A DEPRECATED pragma
         | WarnPragmaDecl   SrcLoc [([Name], String)]
         -- ^ A WARNING pragma
         | InlineSig        SrcLoc Bool Activation QName
         -- ^ An INLINE pragma
         | InlineConlikeSig SrcLoc      Activation QName
         -- ^ An INLINE CONLIKE pragma
         | SpecSig          SrcLoc                 QName [Type]
         -- ^ A SPECIALISE pragma
         | SpecInlineSig    SrcLoc Bool Activation QName [Type]
         -- ^ A SPECIALISE INLINE pragma
         | InstSig          SrcLoc Context         QName [Type]
         -- ^ A SPECIALISE instance pragma
         | AnnPragma        SrcLoc Annotation
         -- ^ An ANN pragma
*/

    syntax Decl ::= `TypeDecl K  K K K
                  | `TypeFamDecl K K K K
                  | `DataDecl K K K K K K K
                  | `GDataDecl K K K K K K K K
                  | `DataFamDecl K K K K K
                  | `TypeInsDecl K K K
                  | `DataInsDecl K K K K K
                  | `GDataInsDecl K K K K K K
                  | `ClassDecl K K  K K K K
                  | `InstDecl K K K K K
                  | `DerivDecl K K K K
                  | `InfixDecl K K K K
                  | `DefaultDecl K K
                  | `SpliceDecl K K
                  | `TypeSig K K K
                  | `FunBind K
                  | `PatBind K K K K K
                  | `ForImp K K K K  K K
                  | `ForExp K K K  K K
                  | `RulePragmaDecl K K
                  | `DeprPragmaDecl K K
                  | `WarnPragmaDecl K K
                  | `InlineSig K K K K
                  | `InlineConlikeSig K K K
                  | `SpecSig K K K
                  | `SpecInlineSig K K K K K
                  | `InstSig K K K K
                  | `AnnPragma K K

/*
    -- | An annotation through an ANN pragma.
    data Annotation
        = Ann       Name Exp
        -- ^ An annotation for a declared name.
        | TypeAnn   Name Exp
        -- ^ An annotation for a declared type.
        | ModuleAnn      Exp
        -- ^ An annotation for the defining module.
*/

    syntax Annotation ::= `Ann K K
                        | `TypeAnn K K
                        | `ModuleAnn K

/*
    -- | A flag stating whether a declaration is a data or newtype declaration.
    data DataOrNew = DataType | NewType
*/

    syntax DataOrNew ::= `DataType
                       | `NewType

/*
    -- | A binding group inside a @let@ or @where@ clause.
    data Binds
        = BDecls [Decl]     -- ^ An ordinary binding group
        | IPBinds [IPBind]  -- ^ A binding group for implicit parameters
*/

    syntax Binds ::= `BDecls K
                   | `IPBinds K

/*
    -- | A binding of an implicit parameter.
    data IPBind = IPBind SrcLoc IPName Exp
*/

    syntax IPBind ::= `IPBind K K K

/*
    -- | Clauses of a function binding.
    data Match
         = Match SrcLoc Name [Pat] (Maybe Type) Rhs {-where-} Binds
*/

    syntax Match ::= `Match K K K K K K

/*
    -- | A single constructor declaration within a data type declaration,
    --   which may have an existential quantification binding.
    data QualConDecl
        = QualConDecl SrcLoc
            {-forall-} [TyVarBind] {- . -} Context
            {- => -} ConDecl
*/

    syntax QualConDecl ::= `QualConDecl K K K K

/*
    -- | Declaration of an ordinary data constructor.
    data ConDecl
         = ConDecl Name [BangType]
                    -- ^ ordinary data constructor
         | InfixConDecl BangType Name BangType
                    -- ^ infix data constructor
         | RecDecl Name [([Name],BangType)]
                    -- ^ record constructor
*/

    syntax ConDecl ::= `ConDecl  K K
                     | `InfixConDecl K K K
                     | `RecDecl  K K

/*
    -- | A single constructor declaration in a GADT data type declaration.
    data GadtDecl
        = GadtDecl SrcLoc Name Type
*/

    syntax GadtDecl ::= `GadtDecl K K K

/*
    -- | Declarations inside a class declaration.
    data ClassDecl
        = ClsDecl    Decl
                -- ^ ordinary declaration
        | ClsDataFam SrcLoc Context Name [TyVarBind] (Maybe Kind)
                -- ^ declaration of an associated data type
        | ClsTyFam   SrcLoc         Name [TyVarBind] (Maybe Kind)
                -- ^ declaration of an associated type synonym
        | ClsTyDef   SrcLoc Type    Type
                -- ^ default choice for an associated type synonym
*/

    syntax ClassDecl ::= `ClsDecl K
                       | `ClsDataFam K K K K K
                       | `ClsTyFam K K K K
                       | `ClsTyDef K K K

/*
    -- | Declarations inside an instance declaration.
    data InstDecl
        = InsDecl   Decl
                -- ^ ordinary declaration
        | InsType   SrcLoc Type Type
                -- ^ an associated type definition
        | InsData   SrcLoc DataOrNew Type [QualConDecl] [Deriving]
                -- ^ an associated data type implementation
        | InsGData  SrcLoc DataOrNew Type (Maybe Kind) [GadtDecl] [Deriving]
                -- ^ an associated data type implemented using GADT style
*/

    syntax InstDecl ::= `InsDecl K
                      | `InsType K K K
                      | `InsData K K K K K
                      | `InsGData K K K K K K

/*
    -- | The type of a constructor argument or field, optionally including
    --   a strictness annotation.
    data BangType
         = BangedTy   Type  -- ^ strict component, marked with \"@!@\"
         | UnBangedTy Type  -- ^ non-strict component
         | UnpackedTy Type  -- ^ unboxed component, marked with an UNPACK pragma
*/

    syntax BangType ::= `BangedTy K
                      | `UnBangedTy K
                      | `UnpackedTy K

/*
    -- | The right hand side of a function or pattern binding.
    data Rhs
         = UnGuardedRhs Exp -- ^ unguarded right hand side (/exp/)
         | GuardedRhss  [GuardedRhs]
                            -- ^ guarded right hand side (/gdrhs/)
*/

    syntax Rhs ::= `UnGuardedRhs K
                 | `GuardedRhss K

/*
    -- | A guarded right hand side @|@ /stmts/ @=@ /exp/.
    --   The guard is a series of statements when using pattern guards,
    --   otherwise it will be a single qualifier expression.
    data GuardedRhs
         = GuardedRhs SrcLoc [Stmt] Exp
*/

    syntax GuardedRhs ::= `GuardedRhs K K K

/*
    -- | A type qualified with a context.
    --   An unqualified type has an empty context.
    data Type
         = TyForall
            (Maybe [TyVarBind])
            Context
            Type                    -- ^ qualified type
         | TyFun   Type Type        -- ^ function type
         | TyTuple Boxed [Type]     -- ^ tuple type, possibly boxed
         | TyList  Type             -- ^ list syntax, e.g. [a], as opposed to [] a
         | TyApp   Type Type        -- ^ application of a type constructor
         | TyVar   Name             -- ^ type variable
         | TyCon   QName            -- ^ named type or type constructor
         | TyParen Type             -- ^ type surrounded by parentheses
         | TyInfix Type QName Type  -- ^ infix type constructor
         | TyKind  Type Kind        -- ^ type with explicit kind signature
*/

    syntax Type ::= `TyForall K K K
                  | `TyFun K K
                  | `TyTuple K K
                  | `TyList K
                  | `TyApp K K
                  | `TyVar  K
                  | `TyCon K
                  | `TyParen K
                  | `TyInfix K K K
                  | `TyKind K K

/*
    -- | A type variable declaration, optionally with an explicit kind annotation.
    data TyVarBind
        = KindedVar Name Kind   -- ^ variable binding with kind annotation
        | UnkindedVar Name      -- ^ ordinary variable binding
*/

    syntax TyVarBind ::= `KindedVar K K
                       | `UnkindedVar K

/*
    -- | An explicit kind annotation.
    data Kind
        = KindStar          -- ^ @*@, the kind of types
        | KindBang          -- ^ @!@, the kind of unboxed types
        | KindFn Kind Kind  -- ^ @->@, the kind of a type constructor
        | KindParen Kind    -- ^ a kind surrounded by parentheses
        | KindVar Name      -- ^ a kind variable (as of yet unsupported by compilers)
*/

    syntax Kind ::= `KindStar
                  | `KindBang
                  | `KindFn K K
                  | `KindParen K
                  | `KindVar K

/*
    -- | A functional dependency, given on the form
    --   l1 l2 ... ln -> r2 r3 .. rn
    data FunDep
        = FunDep [Name] [Name]
*/

    syntax FunDep ::= `FunDep K K

/*
    -- | A context is a set of assertions
    type Context = [Asst]

    note: we're erasing type synonyms
*/

/*
    -- | Class assertions.
    --   In Haskell 98, the argument would be a /tyvar/, but this definition
    --   allows multiple parameters, and allows them to be /type/s.
    --   Also extended with support for implicit parameters and equality constraints.
    data Asst = ClassA QName [Type]     -- ^ ordinary class assertion
              | InfixA Type QName Type  -- ^ class assertion where the class name is given infix
              | IParam IPName Type      -- ^ implicit parameter assertion
              | EqualP Type   Type      -- ^ type equality constraint
*/

    syntax Asst ::= `ClassA K K
                  | `InfixA K K K
                  | `IParam K K
                  | `EqualP K K

/*
    -- | /literal/
    -- Values of this type hold the abstract value of the literal, not the
    -- precise string representation used.  For example, @10@, @0o12@ and @0xa@
    -- have the same representation.
    data Literal
        = Char    Char          -- ^ character literal
        | String  String        -- ^ string literal
        | Int     Integer       -- ^ integer literal
        | Frac    Rational      -- ^ floating point literal
        | PrimInt    Integer    -- ^ unboxed integer literal
        | PrimWord   Integer    -- ^ unboxed word literal
        | PrimFloat  Rational   -- ^ unboxed float literal
        | PrimDouble Rational   -- ^ unboxed double literal
        | PrimChar   Char       -- ^ unboxed character literal
        | PrimString String     -- ^ unboxed string literal
*/

    syntax Literal ::= `Char K
                     | `String K
                     | `Int K
                     | `Frac K
                     | `PrimInt K
                     | `PrimWord K
                     | `PrimFloat K
                     | `PrimDouble K
                     | `PrimChar K
                     | `PrimString K

/*
    -- | Haskell expressions.
    data Exp
        = Var QName                 -- ^ variable
        | IPVar IPName              -- ^ implicit parameter variable
        | Con QName                 -- ^ data constructor
        | Lit Literal               -- ^ literal constant
        | InfixApp Exp QOp Exp      -- ^ infix application
        | App Exp Exp               -- ^ ordinary application
        | NegApp Exp                -- ^ negation expression @-/exp/@ (unary minus)
        | Lambda SrcLoc [Pat] Exp   -- ^ lambda expression
        | Let Binds Exp             -- ^ local declarations with @let@ ... @in@ ...
        | If Exp Exp Exp            -- ^ @if@ /exp/ @then@ /exp/ @else@ /exp/
        | Case Exp [Alt]            -- ^ @case@ /exp/ @of@ /alts/
        | Do [Stmt]                 -- ^ @do@-expression:
                                    --   the last statement in the list
                                    --   should be an expression.
        | MDo [Stmt]                -- ^ @mdo@-expression
        | Tuple [Exp]               -- ^ tuple expression
        | TupleSection [Maybe Exp]  -- ^ tuple section expression, e.g. @(,,3)@
        | List [Exp]                -- ^ list expression
        | Paren Exp                 -- ^ parenthesised expression
        | LeftSection Exp QOp       -- ^ left section @(@/exp/ /qop/@)@
        | RightSection QOp Exp      -- ^ right section @(@/qop/ /exp/@)@
        | RecConstr QName [FieldUpdate]
                                    -- ^ record construction expression
        | RecUpdate Exp [FieldUpdate]
                                    -- ^ record update expression
        | EnumFrom Exp              -- ^ unbounded arithmetic sequence,
                                    --   incrementing by 1: @[from ..]@
        | EnumFromTo Exp Exp        -- ^ bounded arithmetic sequence,
                                    --   incrementing by 1 @[from .. to]@
        | EnumFromThen Exp Exp      -- ^ unbounded arithmetic sequence,
                                    --   with first two elements given @[from, then ..]@
        | EnumFromThenTo Exp Exp Exp
                                    -- ^ bounded arithmetic sequence,
                                    --   with first two elements given @[from, then .. to]@
        | ListComp Exp  [QualStmt]    -- ^ ordinary list comprehension
        | ParComp  Exp [[QualStmt]]   -- ^ parallel list comprehension
        | ExpTypeSig SrcLoc Exp Type  -- ^ expression with explicit type signature

        | VarQuote QName            -- ^ @'x@ for template haskell reifying of expressions
        | TypQuote QName            -- ^ @''T@ for template haskell reifying of types
        | BracketExp Bracket        -- ^ template haskell bracket expression
        | SpliceExp Splice          -- ^ template haskell splice expression
        | QuasiQuote String String  -- ^ quasi-quotaion: @[$/name/| /string/ |]@

    -- Hsx
        | XTag SrcLoc XName [XAttr] (Maybe Exp) [Exp]
                                    -- ^ xml element, with attributes and children
        | XETag SrcLoc XName [XAttr] (Maybe Exp)
                                    -- ^ empty xml element, with attributes
        | XPcdata String            -- ^ PCDATA child element
        | XExpTag Exp               -- ^ escaped haskell expression inside xml

    -- Pragmas
        | CorePragma        String Exp      -- ^ CORE pragma
        | SCCPragma         String Exp      -- ^ SCC pragma
        | GenPragma         String (Int, Int) (Int, Int) Exp
                                            -- ^ GENERATED pragma

    -- Arrows
        | Proc SrcLoc     Pat Exp   -- ^ arrows proc: @proc@ /pat/ @->@ /exp/
        | LeftArrApp      Exp Exp   -- ^ arrow application (from left): /exp/ @-<@ /exp/
        | RightArrApp     Exp Exp   -- ^ arrow application (from right): /exp/ @>-@ /exp/
        | LeftArrHighApp  Exp Exp   -- ^ higher-order arrow application (from left): /exp/ @-<<@ /exp/
        | RightArrHighApp Exp Exp   -- ^ higher-order arrow application (from right): /exp/ @>>-@ /exp/
*/

    syntax Exp ::= `Var K
                 | `IPVar K
                 | `Con K
                 | `Lit K
                 | `InfixApp K K K
                 | `App K K
                 | `NegApp K
                 | `Lambda K K K
                 | `Let K K
                 | `If K K K
                 | `Case K K
                 | `Do K
                 | `MDo K
                 | `Tuple K
                 | `TupleSection K
--- todo: Rename List here to be something else, this will also apply to the output of the parser.
---                 | `List K
                 | `Paren K
                 | `LeftSection K K
                 | `RightSection K K
                 | `RecConstr K K
                 | `RecUpdate K K
                 | `EnumFrom K
                 | `EnumFromTo K K
                 | `EnumFromThen K K
                 | `EnumFromThenTo K K K
                 | `ListComp K K
                 | `ParComp K K
                 | `ExpTypeSig K K K
                 | `VarQuote K
                 | `TypQuote K
                 | `BracketExp K
                 | `SpliceExp K
                 | `QuasiQuote K K
                 | `XTag K K K K K
                 | `XETag K K K K
                 | `XPcdata K
                 | `XExpTag K
                 | `CorePragma K K
                 | `SCCPragma K K
                 | `GenPragma K K K K
                 | `Proc K K K
                 | `LeftArrApp K K
                 | `RightArrApp K K
                 | `LeftArrHighApp K K
                 | `RightArrHighApp K K

/*
    -- | The name of an xml element or attribute,
    --   possibly qualified with a namespace.
    data XName
        = XName String              -- <name ...
        | XDomName String String    -- <dom:name ...
*/

    syntax XName ::= `XName K
                   | `XDomName K K

/*
    -- | An xml attribute, which is a name-expression pair.
    data XAttr = XAttr XName Exp
*/

    syntax XAttr ::= `XAttr K K

/*
    -- | A template haskell bracket expression.
    data Bracket
        = ExpBracket Exp        -- ^ expression bracket: @[| ... |]@
        | PatBracket Pat        -- ^ pattern bracket: @[p| ... |]@
        | TypeBracket Type      -- ^ type bracket: @[t| ... |]@
        | DeclBracket [Decl]    -- ^ declaration bracket: @[d| ... |]@
*/

    syntax Bracket ::= `PatBracket K
                     | `TypeBracket K
                     | `DeclBracket K

/*
    -- | A template haskell splice expression
    data Splice
        = IdSplice String       -- ^ variable splice: @$var@
        | ParenSplice Exp       -- ^ parenthesised expression splice: @$(/exp/)@
*/

    syntax Splice ::= `IdSplice K
                    | `ParenSplice K

/*
    -- | The safety of a foreign function call.
    data Safety
        = PlayRisky         -- ^ unsafe
        | PlaySafe Bool     -- ^ safe ('False') or threadsafe ('True')
*/

    syntax Safety ::= `PlayRisky
                    | `PlaySafe K

/*
    -- | The calling convention of a foreign function call.
    data CallConv
        = StdCall
        | CCall
*/

    syntax CallConv ::= `StdCall
                      | `CCall

/*
    -- | A top level options pragma, preceding the module header.
    data ModulePragma
        = LanguagePragma   SrcLoc [Name]    -- ^ LANGUAGE pragma
        | OptionsPragma    SrcLoc (Maybe Tool) String
                            -- ^ OPTIONS pragma, possibly qualified with a tool, e.g. OPTIONS_GHC
        | AnnModulePragma  SrcLoc Annotation
                            -- ^ ANN pragma with module scope
*/

    syntax ModulePragma ::= `LanguagePragma K K
                          | `OptionsPragma K K K
                          | `AnnModulePragma K K

/*
    -- | Activation clause of a RULES pragma.
    data Activation
        = AlwaysActive
        | ActiveFrom  Int
        | ActiveUntil Int
*/

    syntax Activation ::= `AlwaysActive
                        | `ActiveFrom K
                        | `ActiveUntil K

/*
    -- | The body of a RULES pragma.
    data Rule
        = Rule String Activation (Maybe [RuleVar]) Exp Exp
*/

    syntax Rule ::= `Rule K K K K K

/*
    -- | Variables used in a RULES pragma, optionally annotated with types
    data RuleVar
        = RuleVar Name
        | TypedRuleVar Name Type
*/

    syntax RuleVar ::= `RuleVar  K
                     | `TypedRuleVar  K K

/*
    -- | Warning text to optionally use in the module header of e.g.
    --   a deprecated module.
    data WarningText
        = DeprText String
        | WarnText String
*/

    syntax WarningText ::= `DeprText K
                         | `WarnText K

/*
    -- | A pattern, to be matched against a value.
    data Pat
        = PVar Name                     -- ^ variable
        | PLit Literal                  -- ^ literal constant
        | PNeg Pat                      -- ^ negated pattern
        | PNPlusK Name Integer          -- ^ n+k pattern
        | PInfixApp Pat QName Pat       -- ^ pattern with an infix data constructor
        | PApp QName [Pat]              -- ^ data constructor and argument patterns
        | PTuple [Pat]                  -- ^ tuple pattern
        | PList [Pat]                   -- ^ list pattern
        | PParen Pat                    -- ^ parenthesized pattern
        | PRec QName [PatField]         -- ^ labelled pattern, record style
        | PAsPat Name Pat               -- ^ @\@@-pattern
        | PWildCard                     -- ^ wildcard pattern: @_@
        | PIrrPat Pat                   -- ^ irrefutable pattern: @~/pat/@
        | PatTypeSig SrcLoc Pat Type    -- ^ pattern with type signature
        | PViewPat Exp Pat              -- ^ view patterns of the form @(/exp/ -> /pat/)@
        | PRPat [RPat]                  -- ^ regular list pattern
        | PXTag SrcLoc XName [PXAttr] (Maybe Pat) [Pat]
                                        -- ^ XML element pattern
        | PXETag SrcLoc XName [PXAttr] (Maybe Pat)
                                        -- ^ XML singleton element pattern
        | PXPcdata String               -- ^ XML PCDATA pattern
        | PXPatTag Pat                  -- ^ XML embedded pattern
        | PXRPats [RPat]                -- ^ XML regular list pattern
        | PExplTypeArg QName Type       -- ^ Explicit generics style type argument e.g. @f {| Int |} x = ...@
        | PQuasiQuote String String     -- ^ quasi quote patter: @[$/name/| /string/ |]@
        | PBangPat Pat                  -- ^ strict (bang) pattern: @f !x = ...@
*/

    syntax Pat ::= `PVar  K
                 | `PLit K
                 | `PNeg K
                 | `PNPlusK K K
                 | `PInfixApp K K K
                 | `PApp K K
                 | `PTuple K
                 | `PList K
                 | `PParen K
                 | `PRec K K
                 | `PAsPat K K
                 | `PWildCard
                 | `PIrrPat K
                 | `PatTypeSig K K K
                 | `PViewPat K K
                 | `PRPat K
                 | `PXTag K K K K K
                 | `PXETag K K K K
                 | `PXPcdata K
                 | `PXPatTag K
                 | `PXRPats K
                 | `PExplTypeArg K K
                 | `PQuasiQuote K K
                 | `PBangPat K

/*
    -- | An XML attribute in a pattern.
    data PXAttr = PXAttr XName Pat
*/

    syntax PXAttr ::= `PXAttr K K

/*
    -- | A regular pattern operator.
    data RPatOp
        = RPStar    -- ^ @*@ = 0 or more
        | RPStarG   -- ^ @*!@ = 0 or more, greedy
        | RPPlus    -- ^ @+@ = 1 or more
        | RPPlusG   -- ^ @+!@ = 1 or more, greedy
        | RPOpt     -- ^ @?@ = 0 or 1
        | RPOptG    -- ^ @?!@ = 0 or 1, greedy
*/

    syntax RPatOp ::= `RPStar
                    | `RPStarG
                    | `RPPlus
                    | `RPPlusG
                    | `RPOpt
                    | `RPOptG

/*
    -- | An entity in a regular pattern.
    data RPat
        = RPOp RPat RPatOp      -- ^ operator pattern, e.g. pat*
        | RPEither RPat RPat    -- ^ choice pattern, e.g. (1 | 2)
        | RPSeq [RPat]          -- ^ sequence pattern, e.g. (| 1, 2, 3 |)
        | RPGuard Pat [Stmt]    -- ^ guarded pattern, e.g. (| p | p < 3 |)
        | RPCAs Name RPat       -- ^ non-linear variable binding, e.g. (foo\@:(1 | 2))*
        | RPAs Name RPat        -- ^ linear variable binding, e.g. foo\@(1 | 2)
        | RPParen RPat          -- ^ parenthesised pattern, e.g. (2*)
        | RPPat Pat             -- ^ an ordinary pattern
*/

    syntax RPat ::= `RPOp K K
                  | `RPEither K K
                  | `RPSeq K
                  | `RPGuard K K
                  | `RPCAs  K K
                  | `RPAs  K K
                  | `RPParen K
                  | `RPPat K

/*
    -- | An /fpat/ in a labeled record pattern.
    data PatField
        = PFieldPat QName Pat       -- ^ ordinary label-pattern pair
        | PFieldPun Name            -- ^ record field pun
        | PFieldWildcard            -- ^ record field wildcard
*/

    syntax PatField ::= `PFieldPat K K
                      | `PFieldPun K
                      | `PFieldWildcard

/*
    -- | A statement, representing both a /stmt/ in a @do@-expression,
    --   an ordinary /qual/ in a list comprehension, as well as a /stmt/
    --   in a pattern guard.
    data Stmt
        = Generator SrcLoc Pat Exp
                            -- ^ a generator: /pat/ @<-@ /exp/
        | Qualifier Exp     -- ^ an /exp/ by itself: in a @do@-expression,
                            --   an action whose result is discarded;
                            --   in a list comprehension and pattern guard,
                            --   a guard expression
        | LetStmt Binds     -- ^ local bindings
        | RecStmt [Stmt]    -- ^ a recursive binding group for arrows
*/

    syntax Stmt ::= `Generator K K K
                  | `Qualifier K
                  | `LetStmt K
                  | `RecStmt K

/*
    -- | A general /transqual/ in a list comprehension,
    --   which could potentially be a transform of the kind
    --   enabled by TransformListComp.
    data QualStmt
        = QualStmt     Stmt         -- ^ an ordinary statement
        | ThenTrans    Exp          -- ^ @then@ /exp/
        | ThenBy       Exp Exp      -- ^ @then@ /exp/ @by@ /exp/
        | GroupBy      Exp          -- ^ @then@ @group@ @by@ /exp/
        | GroupUsing   Exp          -- ^ @then@ @group@ @using@ /exp/
        | GroupByUsing Exp Exp      -- ^ @then@ @group@ @by@ /exp/ @using@ /exp/
*/

    syntax QualStmt ::= `QualStmt K
                      | `ThenTrans K
                      | `ThenBy K K
                      | `GroupBy K
                      | `GroupUsing K
                      | `GroupByUsing K K

/*
    -- | An /fbind/ in a labeled construction or update expression.
    data FieldUpdate
        = FieldUpdate QName Exp     -- ^ ordinary label-expresion pair
        | FieldPun Name             -- ^ record field pun
        | FieldWildcard             -- ^ record field wildcard
*/

    syntax FieldUpdate ::= `FieldUpdate K K
                         | `FieldPun  K
                         | `FieldWildcard

/*
    -- | An /alt/ alternative in a @case@ expression.
    data Alt
        = Alt SrcLoc Pat GuardedAlts Binds
*/

    syntax Alt ::= `Alt K K K K

/*
    -- | The right-hand sides of a @case@ alternative,
    --   which may be a single right-hand side or a
    --   set of guarded ones.
    data GuardedAlts
        = UnGuardedAlt Exp          -- ^ @->@ /exp/
        | GuardedAlts  [GuardedAlt] -- ^ /gdpat/
*/

    syntax GuardedAlts ::= `UnGuardedAlt K
                         | `GuardedAlts K

/*
    -- | A guarded case alternative @|@ /stmts/ @->@ /exp/.
    data GuardedAlt
        = GuardedAlt SrcLoc [Stmt] Exp
*/

    syntax GuardedAlt ::= `GuardedAlt K K K

           --- End of syntax, rest of this file is the remainder of Language.Haskell.Exts.Syntax

/*
    -----------------------------------------------------------------------------
    -- Builtin names.

    prelude_mod, main_mod :: ModuleName
    prelude_mod = ModuleName "Prelude"
    main_mod    = ModuleName "Main"

    main_name :: Name
    main_name = Ident "main"

    unit_con_name :: QName
    unit_con_name = Special UnitCon

    tuple_con_name :: Boxed -> Int -> QName
    tuple_con_name b i = Special (TupleCon b (i+1))

    list_cons_name :: QName
    list_cons_name = Special Cons

    unboxed_singleton_con_name :: QName
    unboxed_singleton_con_name = Special UnboxedSingleCon

    unit_con :: Exp
    unit_con = Con unit_con_name

    tuple_con :: Boxed -> Int -> Exp
    tuple_con b i = Con (tuple_con_name b i)

    unboxed_singleton_con :: Exp
    unboxed_singleton_con = Con (unboxed_singleton_con_name)

    as_name, qualified_name, hiding_name, minus_name, bang_name, dot_name, star_name :: Name
    as_name        = Ident "as"
    qualified_name = Ident "qualified"
    hiding_name    = Ident "hiding"
    minus_name     = Symbol "-"
    bang_name      = Symbol "!"
    dot_name       = Symbol "."
    star_name      = Symbol "*"

    export_name, safe_name, unsafe_name, threadsafe_name, stdcall_name, ccall_name :: Name
    export_name     = Ident "export"
    safe_name       = Ident "safe"
    unsafe_name     = Ident "unsafe"
    threadsafe_name = Ident "threadsafe"
    stdcall_name    = Ident "stdcall"
    ccall_name      = Ident "ccall"

    unit_tycon_name, fun_tycon_name, list_tycon_name, unboxed_singleton_tycon_name :: QName
    unit_tycon_name = unit_con_name
    fun_tycon_name  = Special FunCon
    list_tycon_name = Special ListCon
    unboxed_singleton_tycon_name = Special UnboxedSingleCon

    tuple_tycon_name :: Boxed -> Int -> QName
    tuple_tycon_name b i = tuple_con_name b i

    unit_tycon, fun_tycon, list_tycon, unboxed_singleton_tycon :: Type
    unit_tycon = TyCon unit_tycon_name
    fun_tycon  = TyCon fun_tycon_name
    list_tycon = TyCon list_tycon_name
    unboxed_singleton_tycon = TyCon unboxed_singleton_tycon_name

    tuple_tycon :: Boxed -> Int -> Type
    tuple_tycon b i = TyCon (tuple_tycon_name b i)
*/

endkm
