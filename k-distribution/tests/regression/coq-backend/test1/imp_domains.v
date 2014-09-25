Require Import ZArith.
Require Import String.
Require Export maps.

Set Implicit Arguments.
Inductive float : Set :=.

Inductive AExp : Set :=
   k_wrap_Bool_AExp : Bool -> AExp
 | Var : Id -> AExp
 | ACon : Int -> AExp
 | Add : AExp -> AExp -> AExp
 | Div : AExp -> AExp -> AExp
 | k_HOLE_AExp : AExp
with Array : Set :=
   (* 'const-array(_,_) *) k_label_zqconstzmarrayZLzuzxzuZR : Int -> k -> Array
 | (* 'store(_,_,_) *) k_label_zqstoreZLzuzxzuzxzuZR : Array -> Int -> k -> Array
with BExp : Set :=
   BCon : Bool -> BExp
 | k_wrap_Int_BExp : Int -> BExp
 | Not : BExp -> BExp
 | And : BExp -> BExp -> BExp
 | Le : AExp -> AExp -> BExp
 | k_HOLE_BExp : BExp
with Bag : Set :=
with Block : Set :=
   BStmt : Stmt -> Block
 | BEmpty : Block
with Bool : Set :=
   k_wrap_zhBool_Bool : bool -> Bool
 | (* 'exists_._ *) k_label_zqexistszuzizu : k_sort_Set -> Bool -> Bool
 | (* 'forall_._ *) k_label_zqforallzuzizu : k_sort_Set -> Bool -> Bool
with Char : Set :=
with Float : Set :=
   k_wrap_zhFloat_Float : float -> Float
with Id : Set :=
   k_token_Id : string -> Id
with Int : Set :=
   k_wrap_zhInt_Int : Z -> Int
with kitem : Set :=
   k_wrap_zhBool_KItem : bool -> kitem
 | k_wrap_zhFloat_KItem : float -> kitem
 | k_wrap_zhInt_KItem : Z -> kitem
 | k_wrap_zhString_KItem : string -> kitem
 | k_wrap_AExp_KItem : AExp -> kitem
 | k_wrap_Array_KItem : Array -> kitem
 | k_wrap_BExp_KItem : BExp -> kitem
 | k_wrap_Bag_KItem : Bag -> kitem
 | k_wrap_Block_KItem : Block -> kitem
 | k_wrap_Bool_KItem : Bool -> kitem
 | k_wrap_Char_KItem : Char -> kitem
 | k_wrap_Float_KItem : Float -> kitem
 | k_wrap_Id_KItem : Id -> kitem
 | k_wrap_Ids_KItem : list Id -> kitem
 | k_wrap_Int_KItem : Int -> kitem
 | k_wrap_KLabel_KItem : KLabel -> kitem
 | k_wrap_KList_KItem : KList -> kitem
 | k_wrap_List_KItem : List -> kitem
 | k_wrap_MInt_KItem : MInt -> kitem
 | k_wrap_Map_KItem : Map k k -> kitem
 | k_wrap_Nat_KItem : Nat -> kitem
 | k_wrap_Pgm_KItem : Pgm -> kitem
 | k_wrap_Set_KItem : k_sort_Set -> kitem
 | k_wrap_Stmt_KItem : Stmt -> kitem
 | k_wrap_Stream_KItem : Stream -> kitem
 | k_wrap_String_KItem : String -> kitem
 | k_wrap_TCPAnswer_KItem : TCPAnswer -> kitem
 | k_wrap_TCPError_KItem : TCPError -> kitem
 | k_wrap_Variable_KItem : k_sort_Variable -> kitem
 | (* '#ioError(_) *) k_label_zqzhioErrorZLzuZR : String -> kitem
 | (* '#splitedBinder *) k_label_zqzhsplitedBinder : KList -> KList -> k_sort_Set -> kitem
 | (* 'dummy *) k_label_zqdummy : KList -> kitem
 | (* 'freshVariables *) k_label_zqfreshVariables : k_sort_Set -> k -> kitem
 | (* 'isSymbolicK *) k_label_zqisSymbolicK : List -> kitem
 | (* 'select(_,_) *) k_label_zqselectZLzuzxzuZR : Array -> Int -> kitem
 | k_freeze : kitem -> kitem
with KLabel : Set :=
   (* '#_ *) k_label_zqzhzu : k -> KLabel
 | (* '#freezer_ *) k_label_zqzhfreezzerzu : k -> KLabel
 | (* '#symEqualitySort *) k_label_zqzhsymEqualitySort : KLabel
 | (* '#token *) k_label_zqzhtoken : KLabel
 | (* 'cool *) k_label_zqcool : KLabel
 | (* 'heat *) k_label_zqheat : KLabel
 | (* 'heated *) k_label_zqheated : KLabel
 | (* 'isBinder *) k_label_zqisBinder : KLabel
 | (* 'redex *) k_label_zqredex : KLabel
with KList : Set :=
with KResult : Set :=
   k_wrap_Bool_KResult : Bool -> KResult
 | k_wrap_Int_KResult : Int -> KResult
with List : Set :=
with MInt : Set :=
   (* '$mi(_,_) *) k_label_zqzdmiZLzuzxzuZR : Int -> Int -> MInt
with Nat : Set :=
with Pgm : Set :=
   (* 'int_;_ *) k_label_zqintzuZSzu : list Id -> Stmt -> Pgm
with k_sort_Set : Set :=
with Stmt : Set :=
   k_wrap_Block_Stmt : Block -> Stmt
 | Assign : Id -> AExp -> Stmt
 | Seq : Stmt -> Stmt -> Stmt
 | If : BExp -> Block -> Block -> Stmt
 | While : BExp -> Block -> Stmt
with Stream : Set :=
   (* '#buffer *) k_label_zqzhbuffer : k -> Stream
 | (* '#istream *) k_label_zqzhistream : Int -> Stream
 | (* '#noIO *) k_label_zqzhnoIO : Stream
 | (* '#ostream *) k_label_zqzhostream : Int -> Stream
 | (* '#parseInput *) k_label_zqzhparseInput : String -> String -> Stream
with String : Set :=
   k_wrap_zhString_String : string -> String
with TCPAnswer : Set :=
   k_wrap_String_TCPAnswer : String -> TCPAnswer
 | k_wrap_TCPError_TCPAnswer : TCPError -> TCPAnswer
with TCPError : Set :=
   (* '#EACCES *) k_label_zqzhEACCES : TCPError
 | (* '#EBADF *) k_label_zqzhEBADF : TCPError
 | (* '#EINVAL *) k_label_zqzhEINVAL : TCPError
 | (* '#EISDIR *) k_label_zqzhEISDIR : TCPError
 | (* '#ELOOP *) k_label_zqzhELOOP : TCPError
 | (* '#ENAMETOOLONG *) k_label_zqzhENAMETOOLONG : TCPError
 | (* '#ENOENT *) k_label_zqzhENOENT : TCPError
 | (* '#ENOTDIR *) k_label_zqzhENOTDIR : TCPError
 | (* '#EOF *) k_label_zqzhEOF : TCPError
 | (* '#ESPIPE *) k_label_zqzhESPIPE : TCPError
 | (* '#noparse *) k_label_zqzhnoparse : TCPError
 | (* '#tcpError(_) *) k_label_zqzhtcpErrorZLzuZR : String -> TCPError
with k_sort_Variable : Set :=
   k_wrap_Id_Variable : Id -> k_sort_Variable
with k : Set := kdot | kra : kitem -> k -> k
 .

Definition k_inj_Variable_KItem (x : k_sort_Variable) : kitem :=
  match x with
  | k_wrap_Id_Variable i => k_wrap_Id_KItem i
  end.
Definition k_proj_Variable_KItem (x : kitem) : option k_sort_Variable :=
  match x with
  | k_wrap_Id_KItem i => Some (k_wrap_Id_Variable i)
  | k_wrap_Variable_KItem i => Some i
  | _ => None
  end.
Definition k_inj_Stmt_KItem (x : Stmt) : kitem :=
  match x with
  | k_wrap_Block_Stmt i => k_wrap_Block_KItem i
  | _ => k_wrap_Stmt_KItem x
  end.
Definition k_proj_Stmt_KItem (x : kitem) : option Stmt :=
  match x with
  | k_wrap_Block_KItem i => Some (k_wrap_Block_Stmt i)
  | k_wrap_Stmt_KItem i => Some i
  | _ => None
  end.
Definition k_inj_String_KItem (x : String) : kitem :=
  match x with
  | k_wrap_zhString_String i => k_wrap_zhString_KItem i
  end.
Definition k_proj_String_KItem (x : kitem) : option String :=
  match x with
  | k_wrap_zhString_KItem i => Some (k_wrap_zhString_String i)
  | k_wrap_String_KItem i => Some i
  | _ => None
  end.
Definition k_inj_TCPAnswer_KItem (x : TCPAnswer) : kitem :=
  match x with
  | k_wrap_String_TCPAnswer i => k_inj_String_KItem i
  | k_wrap_TCPError_TCPAnswer i => k_wrap_TCPError_KItem i
  end.
Definition k_proj_TCPAnswer_KItem (x : kitem) : option TCPAnswer :=
  match x with
  | k_wrap_zhString_KItem i => Some (k_wrap_String_TCPAnswer (k_wrap_zhString_String i))
  | k_wrap_String_KItem i => Some (k_wrap_String_TCPAnswer i)
  | k_wrap_TCPAnswer_KItem i => Some i
  | k_wrap_TCPError_KItem i => Some (k_wrap_TCPError_TCPAnswer i)
  | _ => None
  end.
Definition k_inj_Int_KItem (x : Int) : kitem :=
  match x with
  | k_wrap_zhInt_Int i => k_wrap_zhInt_KItem i
  end.
Definition k_proj_Int_KItem (x : kitem) : option Int :=
  match x with
  | k_wrap_zhInt_KItem i => Some (k_wrap_zhInt_Int i)
  | k_wrap_Int_KItem i => Some i
  | _ => None
  end.
Definition k_inj_Float_KItem (x : Float) : kitem :=
  match x with
  | k_wrap_zhFloat_Float i => k_wrap_zhFloat_KItem i
  end.
Definition k_proj_Float_KItem (x : kitem) : option Float :=
  match x with
  | k_wrap_zhFloat_KItem i => Some (k_wrap_zhFloat_Float i)
  | k_wrap_Float_KItem i => Some i
  | _ => None
  end.
Definition k_inj_Bool_KItem (x : Bool) : kitem :=
  match x with
  | k_wrap_zhBool_Bool i => k_wrap_zhBool_KItem i
  | _ => k_wrap_Bool_KItem x
  end.
Definition k_proj_Bool_KItem (x : kitem) : option Bool :=
  match x with
  | k_wrap_zhBool_KItem i => Some (k_wrap_zhBool_Bool i)
  | k_wrap_Bool_KItem i => Some i
  | _ => None
  end.
Definition k_inj_KResult_KItem (x : KResult) : kitem :=
  match x with
  | k_wrap_Bool_KResult i => k_inj_Bool_KItem i
  | k_wrap_Int_KResult i => k_inj_Int_KItem i
  end.
Definition k_proj_KResult_KItem (x : kitem) : option KResult :=
  match x with
  | k_wrap_zhBool_KItem i => Some (k_wrap_Bool_KResult (k_wrap_zhBool_Bool i))
  | k_wrap_zhInt_KItem i => Some (k_wrap_Int_KResult (k_wrap_zhInt_Int i))
  | k_wrap_Bool_KItem i => Some (k_wrap_Bool_KResult i)
  | k_wrap_Int_KItem i => Some (k_wrap_Int_KResult i)
  | _ => None
  end.
Definition k_inj_KResult_AExp (x : KResult) : AExp :=
  match x with
  | k_wrap_Bool_KResult i => k_wrap_Bool_AExp i
  | k_wrap_Int_KResult i => ACon i
  end.
Definition k_proj_KResult_AExp (x : AExp) : option KResult :=
  match x with
  | k_wrap_Bool_AExp i => Some (k_wrap_Bool_KResult i)
  | ACon i => Some (k_wrap_Int_KResult i)
  | _ => None
  end.
Definition k_inj_KResult_BExp (x : KResult) : BExp :=
  match x with
  | k_wrap_Bool_KResult i => BCon i
  | k_wrap_Int_KResult i => k_wrap_Int_BExp i
  end.
Definition k_proj_KResult_BExp (x : BExp) : option KResult :=
  match x with
  | BCon i => Some (k_wrap_Bool_KResult i)
  | k_wrap_Int_BExp i => Some (k_wrap_Int_KResult i)
  | _ => None
  end.
Definition k_inj_BExp_KItem (x : BExp) : kitem :=
  match x with
  | BCon i => k_inj_Bool_KItem i
  | k_wrap_Int_BExp i => k_inj_Int_KItem i
  | _ => k_wrap_BExp_KItem x
  end.
Definition k_proj_BExp_KItem (x : kitem) : option BExp :=
  match x with
  | k_wrap_zhBool_KItem i => Some (BCon (k_wrap_zhBool_Bool i))
  | k_wrap_zhInt_KItem i => Some (k_wrap_Int_BExp (k_wrap_zhInt_Int i))
  | k_wrap_BExp_KItem i => Some i
  | k_wrap_Bool_KItem i => Some (BCon i)
  | k_wrap_Int_KItem i => Some (k_wrap_Int_BExp i)
  | _ => None
  end.
Definition k_inj_AExp_KItem (x : AExp) : kitem :=
  match x with
  | k_wrap_Bool_AExp i => k_inj_Bool_KItem i
  | Var i => k_wrap_Id_KItem i
  | ACon i => k_inj_Int_KItem i
  | _ => k_wrap_AExp_KItem x
  end.
Definition k_proj_AExp_KItem (x : kitem) : option AExp :=
  match x with
  | k_wrap_zhBool_KItem i => Some (k_wrap_Bool_AExp (k_wrap_zhBool_Bool i))
  | k_wrap_zhInt_KItem i => Some (ACon (k_wrap_zhInt_Int i))
  | k_wrap_AExp_KItem i => Some i
  | k_wrap_Bool_KItem i => Some (k_wrap_Bool_AExp i)
  | k_wrap_Id_KItem i => Some (Var i)
  | k_wrap_Int_KItem i => Some (ACon i)
  | _ => None
  end.
