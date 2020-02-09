module AbsBlu where

--
-- Haskell module originally generated by the BNF converter and then adapted
--

import Text.PrettyPrint

class PrettyPrintable a where

  toDoc :: a -> Doc

  prettyPrint :: a -> String
  prettyPrint = toString

  toString :: a -> String
  toStringS :: a -> ShowS
  toString = show . toDoc
  toStringS = shows . toDoc

-- indentation tabulation length
tabLen = 2

newtype PIdent = PIdent ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PIdent where
  toDoc (PIdent (_,str)) = text str

newtype PInteger = PInteger ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PInteger where
  toDoc (PInteger (_,str)) = text str

newtype PReal = PReal ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PReal where
  toDoc (PReal (_,str)) = text str

newtype PChar = PChar ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PChar where
  toDoc (PChar (_,str)) = text str

newtype PString = PString ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PString where
  toDoc (PString (_,str)) = text str

newtype PBool = PBool ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PBool where
  toDoc (PBool (_,str)) = text str

newtype PBreak = PBreak ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PBreak where
  toDoc (PBreak (_,str)) = text str

newtype PContinue = PContinue ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PContinue where
  toDoc (PContinue (_,str)) = text str

newtype PWriteInt = PWriteInt ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PWriteInt where
  toDoc (PWriteInt (_,str)) = text str

newtype PWriteFloat = PWriteFloat ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PWriteFloat where
  toDoc (PWriteFloat (_,str)) = text str

newtype PWriteChar = PWriteChar ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PWriteChar where
  toDoc (PWriteChar (_,str)) = text str

newtype PWriteString = PWriteString ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PWriteString where
  toDoc (PWriteString (_,str)) = text str

newtype PReadInt = PReadInt ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PReadInt where
  toDoc (PReadInt (_,str)) = text str

newtype PReadFloat = PReadFloat ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PReadFloat where
  toDoc (PReadFloat (_,str)) = text str

newtype PReadChar = PReadChar ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PReadChar where
  toDoc (PReadChar (_,str)) = text str

newtype PReadString = PReadString ((Int,Int),String)
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable PReadString where
  toDoc (PReadString (_,str)) = text str

data Program = Prog ConstDecls VarDecls FunDecls
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable Program where
  toDoc (Prog cds vds fds) = toDoc cds $+$ toDoc vds $+$ toDoc fds

data ConstDecls = ConstEmpty | ConstBlk [ConstDecl]
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable ConstDecls where
  toDoc ConstEmpty = empty
  toDoc (ConstBlk cds) = text "const" $+$ nest tabLen (vcat (map toDoc cds)) $+$ text "end const"

data ConstDecl = ConstD (Int,Int) PIdent Type RExpr
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable ConstDecl where
  toDoc (ConstD _ i t re) = toDoc i <+> text ":" <+> toDoc t <+> text ":=" <+> toDoc re <+> semi

data VarDecls = VarEmpty | VarBlk [VarDecl]
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable VarDecls where
  toDoc VarEmpty = empty
  toDoc (VarBlk vds) = text "var" $+$ nest tabLen (vcat (map toDoc vds)) $+$ text "end var"

data VarDecl = VarD (Int,Int) PIdent Type MaybeInit
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable VarDecl where
  toDoc (VarD _ i t mi) = toDoc i <+> text ":" <+> toDoc t <+> toDoc mi <+> semi

data MaybeInit = NoInit | JustInit (Int,Int) RExpr
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable MaybeInit where
  toDoc NoInit = empty
  toDoc (JustInit _ re) = text ":=" <+> toDoc re

data FunDecls = FunBlkEmpty | FunBlk [FunDecl]
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable FunDecls where
  toDoc FunBlkEmpty = empty
  toDoc (FunBlk fds) = text "routines" $+$ nest tabLen (vcat (map toDoc fds)) $+$ text "end routines"

data FunDecl = FunD (Int,Int) PIdent MaybeParamsIn MaybeParamsOut FBody PIdent
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable FunDecl where
  toDoc (FunD _ i mpi mpo b i') = toDoc i <+> toDoc mpi <+> toDoc mpo <+> text "is" $+$ nest tabLen (toDoc b) $+$ text "end" <+> toDoc i'

data MaybeParamsIn = NoParamsIn | JustParamsIn [ParamIn]
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable MaybeParamsIn where
  toDoc NoParamsIn = empty
  toDoc (JustParamsIn ps) = parens (hsep (punctuate comma (map toDoc ps)))

data ParamIn = ParamIn (Int,Int) Modality PIdent Type
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable ParamIn where
  toDoc (ParamIn _ m i t) = toDoc m <+> toDoc i <+> text ":" <+> toDoc t

data Modality = ValMod | ValResMod | ConstMod
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable Modality where
  toDoc ValMod = empty
  toDoc ValResMod = text "valres"
  toDoc ConstMod = text "const"

data MaybeParamsOut = NoParamsOut | JustParamsOut [ParamOut]
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable MaybeParamsOut where
  toDoc NoParamsOut = empty
  toDoc (JustParamsOut ps) = text "->" <+> parens (hsep (punctuate comma (map toDoc ps)))

data ParamOut = ParamOut (Int,Int) PIdent Type
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable ParamOut where
  toDoc (ParamOut _ i t) = toDoc i <+> text ":" <+> toDoc t

data FBody = FunBody ConstDecls VarDecls FunDecls [Stmt]
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable FBody where
  toDoc (FunBody cds vds fds stmts) = toDoc cds $+$ toDoc vds $+$ toDoc fds $+$ text "do" $+$ nest tabLen (vcat (map toDoc stmts))

data Stmt
    = StmFCall FunCall
    | Break PBreak
    | Continue PContinue
    | GoTo PIdent
    | Label PIdent
    | While RExpr [Stmt]
    | DoWhile [Stmt] RExpr
    | For ForAss RExpr ForAss [Stmt]
    | If RExpr [Stmt] MaybeElseIf MaybeElse
    | Assgn [LExpr] Ass_Op RExpr
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable Stmt where
  toDoc (StmFCall fc) = toDoc fc <> semi
  toDoc (Break _) = text "break" <> semi
  toDoc (Continue _) = text "continue" <> semi
  toDoc (GoTo i) = text "goto" <+> toDoc i <> semi
  toDoc (Label i) = text "label" <+> toDoc i <+> text ":"
  toDoc (While re stmts) = text "while" <+> parens (toDoc re) <+> text "do" $+$ nest tabLen (vcat (map toDoc stmts)) $+$ text "end while"
  toDoc (DoWhile stmts re) = text "do" $+$ nest tabLen (vcat (map toDoc stmts)) $+$ text "while" <+>  parens (toDoc re)
  toDoc (For a' re a'' stmts) = text "for" <+> parens (toDoc a' <+> comma <+> toDoc re <+> comma <+> toDoc a'' ) <+> text "do" $+$ nest tabLen (vcat (map toDoc stmts)) $+$ text "end for"
  toDoc (If re stmts mei me) = text "if" <+> parens (toDoc re) <+> text "then" $+$ nest tabLen (vcat (map toDoc stmts)) $+$ toDoc mei $+$ toDoc me $+$ text "end if"
  toDoc (Assgn les o re) = hsep (punctuate comma (map toDoc les)) <+> toDoc o <+> toDoc re <+> semi

data MaybeElseIf = NoElseIf | ElseIf RExpr [Stmt] MaybeElseIf
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable MaybeElseIf where
  toDoc NoElseIf = empty
  toDoc (ElseIf re stmts mei) = text "else if" <+> parens (toDoc re) <+> text "then" $+$ nest tabLen (vcat (map toDoc stmts)) $+$ toDoc mei

data MaybeElse = NoElse | Else [Stmt]
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable MaybeElse where
  toDoc NoElse = empty
  toDoc (Else stmts) = text "else" $+$ nest tabLen (vcat (map toDoc stmts))

data ForAss = ForAssgn LExpr Ass_Op RExpr
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable ForAss where
  toDoc (ForAssgn le o re) = toDoc le <+> toDoc o <+> toDoc re

data Ass_Op
    = Assign
    | AssignMul
    | AssignAdd
    | AssignDiv
    | AssignSub
    | AssignPow
    | AssignAnd
    | AssignOr
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable Ass_Op where
  toDoc Assign = text ":="
  toDoc AssignMul = text "*:="
  toDoc AssignAdd = text "+:="
  toDoc AssignDiv = text "/:="
  toDoc AssignSub = text "-:="
  toDoc AssignPow = text "^:="
  toDoc AssignAnd = text "&:="
  toDoc AssignOr = text "|:="

data Type = TArr Type MaybeSize | TPt Type | TBasic BasicType | TVoid
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable Type where
  toDoc (TArr t ms) = text "Array" <+> text "<" <> toDoc t <> text ">" <+> text "(" <> toDoc ms <> text ")"
  toDoc (TPt t) = text "Pt" <+> text "<" <> toDoc t <> text ">"
  toDoc (TBasic bt) = toDoc bt
  toDoc TVoid = text "void"

data MaybeSize = ArrNoSize | ArrSize (Int,Int) RExpr
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable MaybeSize where
  toDoc ArrNoSize = empty
  toDoc (ArrSize _ re) = toDoc re

data BasicType = TBool | TChar | TString | TReal | TInt
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable BasicType where
  toDoc TBool = text "bool"
  toDoc TChar = text "char"
  toDoc TString = text "string"
  toDoc TReal = text "real"
  toDoc TInt = text "int"


data Label = TLabel
  deriving (Eq, Show, Read)

data RExpr
    = Or (Int,Int) RExpr RExpr
    | And (Int,Int) RExpr RExpr
    | Eq (Int,Int) RExpr RExpr
    | NEq (Int,Int) RExpr RExpr
    | Lt (Int,Int) RExpr RExpr
    | LEq (Int,Int) RExpr RExpr
    | Gt (Int,Int) RExpr RExpr
    | GEq (Int,Int) RExpr RExpr
    | Add (Int,Int) RExpr RExpr
    | Sub (Int,Int) RExpr RExpr
    | Mul (Int,Int) RExpr RExpr
    | Div (Int,Int) RExpr RExpr
    | Mod (Int,Int) RExpr RExpr
    | RexprCall (Int,Int) FunCall
    | ArrayElems [RExpr]
    | AddrOf (Int,Int) LExpr
    | Not (Int,Int) RExpr
    | UnMin (Int,Int) RExpr
    | UnPlus (Int,Int) RExpr
    | Lexpr (Int,Int) LExpr
    | Integer (Int,Int) PInteger
    | Real (Int,Int) PReal
    | Char (Int,Int) PChar
    | String (Int,Int) PString
    | Bool (Int,Int) PBool
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable RExpr where
  toDoc (Or _ re' re'') = toDoc re' <+> text "||" <+> toDoc re''
  toDoc (And _ re' re'') = toDoc re' <+> text "&&" <+> toDoc re''
  toDoc (Eq _ re' re'') = toDoc re' <+> text "=" <+> toDoc re''
  toDoc (NEq _ re' re'') = toDoc re' <+> text "<>" <+> toDoc re''
  toDoc (Lt _ re' re'') = toDoc re' <+> text "<" <+> toDoc re''
  toDoc (LEq _ re' re'') = toDoc re' <+> text "<=" <+> toDoc re''
  toDoc (Gt _ re' re'') = toDoc re' <+> text ">" <+> toDoc re''
  toDoc (GEq _ re' re'') = toDoc re' <+> text ">=" <+> toDoc re''
  toDoc (Add _ re' re'') = toDoc re' <+> text "+" <+> toDoc re''
  toDoc (Sub _ re' re'') = toDoc re' <+> text "-" <+> toDoc re''
  toDoc (Mul _ re' re'') = toDoc re' <+> text "*" <+> toDoc re''
  toDoc (Div _ re' re'') = toDoc re' <+> text "/" <+> toDoc re''
  toDoc (Mod _ re' re'') = toDoc re' <+> text "%" <+> toDoc re''
  toDoc (RexprCall _ fc) = toDoc fc
  toDoc (ArrayElems res@((ArrayElems elems):_)) = brackets (vcat (map toDoc res))
  toDoc (ArrayElems res) = brackets (hsep (punctuate comma (map toDoc res)))
  toDoc (AddrOf _ le) = text "&" <> toDoc le
  toDoc (Not _ re) = text "!" <+> toDoc re
  toDoc (UnMin _ re) = text "-" <> toDoc re
  toDoc (UnPlus _ re) = text "+" <> toDoc re
  toDoc (Lexpr _ le) = toDoc le
  toDoc (Integer _ n) = toDoc n
  toDoc (Real _ q) = toDoc q
  toDoc (Char _ c) = toDoc c
  toDoc (String _ s) = toDoc s
  toDoc (Bool _ b) = toDoc b

data FunCall
    = UserDefFCall PIdent [RExpr]
    | WIntCall PWriteInt RExpr
    | WFloatCall PWriteFloat RExpr
    | WCharCall PWriteChar RExpr
    | WStringCall PWriteString RExpr
    | RIntCall PReadInt
    | RFloatCall PReadFloat
    | RCharCall PReadChar
    | RStringCall PReadString
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable FunCall where
  toDoc (UserDefFCall fId res) = toDoc fId <+> parens (hsep (punctuate comma (map toDoc res)))
  toDoc (WIntCall fId re) = toDoc fId <+> parens (toDoc re)
  toDoc (WFloatCall fId re) = toDoc fId <+> parens (toDoc re)
  toDoc (WCharCall fId re) = toDoc fId <+> parens (toDoc re)
  toDoc (WStringCall fId re) = toDoc fId <+> parens (toDoc re)
  toDoc (RIntCall fId) = toDoc fId <+> parens empty
  toDoc (RFloatCall fId) = toDoc fId <+> parens empty
  toDoc (RCharCall fId) = toDoc fId <+> parens empty
  toDoc (RStringCall fId) = toDoc fId <+> parens empty

data LExpr = Deref (Int,Int) RExpr | ElemAt (Int,Int) LExpr RExpr | Var (Int,Int) PIdent
  deriving (Eq, Ord, Show, Read)
instance PrettyPrintable LExpr where
  toDoc (Deref _ re) = text "$" <> toDoc re
  toDoc (ElemAt _ le re) = toDoc le <> brackets (toDoc re)
  toDoc (Var _ i) = toDoc i