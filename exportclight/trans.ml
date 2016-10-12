(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Pretty-printer for Clight/Csyntax *)

open Camlcoq
open Datatypes
open Values
open AST
open PrintAST
open Ctypes
open Cop
open Csyntax
open Globalenvs
open Format

let temp_name (id: AST.ident) = "_" ^ Z.to_string (Z.Zpos id)

let extern_atom a =
  try
    Hashtbl.find string_of_atom a
  with Not_found ->
    Printf.sprintf "_%d" (P.to_int a)

type trans = 
  | Skip
  | Decl of trans
  | Def of trans * trans * (string * trans) list
  | Trans of trans list * trans list * trans list
  | Ext of string * trans * trans * trans
  | Tfun of string * trans * (string * trans) list * (string * trans) list * (string * trans) list * trans list
  | Reg of string * trans
  | Nam of string * trans
  | Var of string * trans
  | Space of int
  | Char of int
  | Short of int
  | Long of int32
  | LongLong of int64
  | Float of float
  | Double of float
  | Addrof of string * int32
  | Assign of trans * trans * trans
  | Set of string * trans
  | Call of trans * trans list * trans
  | Sequence of trans * trans
  | Extern of string * trans list * trans list
  | Builtin of string * trans list * trans list * trans
  | Volatile_load of string * trans list * trans list
  | Volatile_store of string * trans list * trans list
  | Malloc of trans list * trans list
  | Free of trans list * trans list
  | Memcpy of int * int * trans list * trans list
  | Annot of string * trans list * trans list
  | Annot_val of string * trans list * trans list
  | Inline_asm of string * trans list * trans list
  | Debug of int * string * trans list * trans list
  | Ifthenelse of trans * trans * trans
  | While of trans * trans
  | For of trans * trans * trans * trans
  | Break
  | Continue
  | Switch of trans * trans list
  | Return of trans
  | Label of string * trans
  | Goto of string
  | Case of string * trans
  | Default of trans
  | Deref of trans * trans
  | Field of trans * string * trans
  | Const_int of int32 * trans
  | Const_float of float * trans
  | Const_long of int64 * trans
  | Const_ptr of int64 * trans
  | Const_single of float * trans
  | Tnotbool of trans * trans
  | Tnotint of trans * trans
  | Tneg of trans * trans
  | Tabs of trans * trans
  | Taddrof of trans * trans
  | Taddlst of trans * trans list
  | Tadd of trans * trans * trans
  | Tsub of trans * trans * trans
  | Tmul of trans * trans * trans
  | Tdiv of trans * trans * trans
  | Tmod of trans * trans * trans
  | Tand of trans * trans * trans
  | Tor  of trans * trans * trans
  | Txor of trans * trans * trans
  | Tshl of trans * trans * trans
  | Tshr of trans * trans * trans
  | Teq  of trans * trans * trans
  | Tne  of trans * trans * trans
  | Tlt  of trans * trans * trans
  | Tgt  of trans * trans * trans
  | Tle  of trans * trans * trans
  | Tge  of trans * trans * trans
  | Cast of trans * trans
  | Sizeof of trans * trans
  | Alignof of trans * trans
  | Alignas of int32
  | Attr of bool * trans
  | Array of trans * int32 * trans
  | Tbool of trans
  | Tparams of string * trans * trans list
  | Tcallconv of bool * bool * bool
  | Tcc_default
  | Tdouble of trans
  | Tfloat of trans
  | Tfunc of trans list * trans * trans
  | The
  | This
  | Schar of trans
  | Sshort of trans
  | Sint of trans
  | Slong of trans
  | Tpointer
  | Tptr of trans * trans
  | Tstruc of string * trans
  | Uchar of trans
  | Ushort of trans
  | Uint of trans
  | Ulong of trans
  | Tuni of string * trans
  | Void
  | Tvolatile
  | Tvolatile_alignas of int32
  | Val of trans * trans
  | Valof of trans * trans
  | Seqand of trans * trans * trans
  | Seqor of trans * trans * trans
  | Condition of trans * trans * trans * trans
  | Assignop of binary_operation * trans * trans * trans * trans
  | Postincr of trans * trans
  | Postdecr of trans * trans
  | Comma of trans * trans * trans
  | Loc of int32 * int32 * trans
  | Paren of trans * trans * trans

let struct_or_union id = function Struct -> Tstruc(id, Void) | Union -> Tuni(id, Void)

let coqN n = N.to_int32 n

let coqint n = camlint_of_coqint n

let coqint64 n = camlint64_of_coqint n

let coqfloat n = Int64.float_of_bits (coqint64 (Floats.Float.to_bits n))

let coqsingle n = Int32.float_of_bits (coqint (Floats.Float32.to_bits n))

let attributes = function
  | { attr_volatile = false; attr_alignas = None} ->
        Void
  | { attr_volatile = true; attr_alignas = None} ->
        Tvolatile
  | { attr_volatile = false; attr_alignas = Some n} ->
        Alignas(coqN n)
  | { attr_volatile = true; attr_alignas = Some n} ->
        Tvolatile_alignas(coqN n)

let typ t = attributes (attr_of_type t)

let rec rtyp = function
  | Tvoid -> Void
  | Tint(sz, sg, a') -> let a = attributes a' in
      (
        match sz, sg with
        | I8, Signed -> Schar a
        | I8, Unsigned -> Uchar a
        | I16, Signed -> Sshort a
        | I16, Unsigned -> Ushort a
        | I32, Signed -> Sint a
        | I32, Unsigned -> Uint a
        | IBool, _ -> Tbool a)
  | Tlong(sg, a') -> let a = attributes a' in
      (
        match sg with
        | Signed -> Slong a
        | Unsigned -> Ulong a)
  | Tfloat(sz, a') -> let a = attributes a' in
      (
        match sz with
        | F32 -> Tfloat a
        | F64 -> Tdouble a)
  | Tpointer(t, a) -> Tptr (typ t, attributes a)
  | Tarray(t, sz, a) -> Array(typ t, Z.to_int32 sz, attributes a)
  | Tfunction(targs, tres, cc) -> Tfunc(typlist targs, typ tres, callconv cc)
  | Tstruct(id, a) -> Tstruc(extern_atom id, attributes a)
  | Tunion(id, a) -> Tuni(extern_atom id, attributes a)

and typlist = function
  | Tnil -> []
  | Tcons(t, tl) -> typ t :: typlist tl

and callconv cc =
  if cc = AST.cc_default
  then Tcc_default
  else Tcallconv(cc.cc_vararg, cc.cc_unproto, cc.cc_structret)

let rec add_list = function
| Tadd(Tadd(lft',rght',typ'),Tadd(lft'',rght'',typ''),typ) when typ=typ' && typ'=typ'' -> Taddlst (typ,[lft';rght';lft'';rght''])
| Tadd(Tadd(lft',rght',typ'),rght,typ) when typ=typ' -> Taddlst (typ,[lft';rght';rght])
| Tadd(lft,Tadd(lft',rght',typ'),typ) when typ=typ' -> Taddlst (typ,[lft;lft';rght'])
| oth -> oth

let rec mapexprlist f = function
| Enil -> []
| Econs(expr, exprlist) -> f expr :: mapexprlist f exprlist

let rec texpr = function
  | Evar(id, t) -> Var(extern_atom id, typ t)
  | Ederef(a1, t) -> Deref(texpr a1, typ t)
  | Efield(a1, f, t) -> Field(texpr a1, extern_atom f, typ t)
(*
  | Econst_int(n, t) -> Const_int(coqint n, typ t)
  | Econst_float(n, t) -> Const_float(coqfloat n, typ t)
  | Econst_long(n, t) -> Const_long(coqint64 n, typ t)
  | Econst_single(n, t) -> Const_single(coqsingle n, typ t)
*)
  | Eunop(Onotbool, a1, t) -> Tnotbool(texpr a1, typ t)
  | Eunop(Onotint, a1, t) -> Tnotint(texpr a1, typ t)
  | Eunop(Oneg, a1, t) -> Tneg(texpr a1, typ t)
  | Eunop(Oabsfloat, a1, t) -> Tabs(texpr a1, typ t)
  | Eaddrof(a1, t) -> Taddrof(texpr a1, typ t)
  | Ebinop(Oadd, a1, a2, t) -> add_list (Tadd(texpr a1, texpr a2, typ t))
  | Ebinop(Osub, a1, a2, t) -> Tsub(texpr a1, texpr a2, typ t)
  | Ebinop(Omul, a1, a2, t) -> Tmul(texpr a1, texpr a2, typ t)
  | Ebinop(Odiv, a1, a2, t) -> Tdiv(texpr a1, texpr a2, typ t)
  | Ebinop(Omod, a1, a2, t) -> Tmod(texpr a1, texpr a2, typ t)
  | Ebinop(Oand, a1, a2, t) -> Tand(texpr a1, texpr a2, typ t)
  | Ebinop(Oor , a1, a2, t) -> Tor (texpr a1, texpr a2, typ t)
  | Ebinop(Oxor, a1, a2, t) -> Txor(texpr a1, texpr a2, typ t)
  | Ebinop(Oshl, a1, a2, t) -> Tshl(texpr a1, texpr a2, typ t)
  | Ebinop(Oshr, a1, a2, t) -> Tshr(texpr a1, texpr a2, typ t)
  | Ebinop(Oeq , a1, a2, t) -> Teq (texpr a1, texpr a2, typ t)
  | Ebinop(One , a1, a2, t) -> Tne (texpr a1, texpr a2, typ t)
  | Ebinop(Olt , a1, a2, t) -> Tlt (texpr a1, texpr a2, typ t)
  | Ebinop(Ogt , a1, a2, t) -> Tgt (texpr a1, texpr a2, typ t)
  | Ebinop(Ole , a1, a2, t) -> Tle (texpr a1, texpr a2, typ t)
  | Ebinop(Oge , a1, a2, t) -> Tge (texpr a1, texpr a2, typ t)
  | Ecast(a1, t) -> Cast(texpr a1, typ t)
  | Esizeof(t1, t) -> Sizeof(typ t1, typ t)
  | Ealignof(t1, t) -> Alignof(typ t1, typ t)
  | Eval (Vint n, ty) -> let ty' = typ ty in Val(Const_int (camlint_of_coqint n, ty'), ty')
  | Eval (Vlong n, ty) -> let ty' = typ ty in Val(Const_long (camlint64_of_coqint n, ty'), ty')
  | Eval (Vptr (n,off), ty) -> let ty' = typ ty in Val(Const_ptr (P.to_int64 n, ty'), ty')
  | Eval (Vfloat n, ty) -> let ty' = typ ty in Val(Const_float (camlfloat_of_coqfloat n, ty'), ty')
  | Eval (Vsingle n, ty) -> let ty' = typ ty in Val(Const_float (camlfloat_of_coqfloat32 n, ty'), ty')
  | Eval (n, ty) -> let ty' = typ ty in failwith "Eval"
  | Evalof (exp, ty) -> Valof(texpr exp, typ ty)
  | Eseqand (e1, e2, ty) -> Seqand(texpr e1, texpr e2, typ ty)
  | Eseqor (e1, e2, ty) -> Seqor(texpr e1, texpr e2, typ ty)
  | Econdition (e1, e2, e3, ty) -> Condition(texpr e1, texpr e2, texpr e3, typ ty)
  | Eassign (e1, e2, ty) -> Assign(texpr e1, texpr e2, typ ty)
  | Eassignop (op, e1, e2, ty1, ty2) -> Assignop(op, texpr e1, texpr e2, typ ty1, typ ty2)
  | Epostincr (Incr, e1, ty) -> Postincr(texpr e1, typ ty)
  | Epostincr (Decr, e1, ty) -> Postdecr(texpr e1, typ ty)
  | Ecomma (e1, e2, ty) -> Comma(texpr e1, texpr e2, typ ty)
  | Ecall (e1, el, ty) -> Call(texpr e1, mapexprlist texpr el, typ ty)
  | Ebuiltin (ef, tyl, el, ty) -> builtin tyl el ty ef
  | Eloc (blk, n, ty) -> Loc(P.to_int32 blk, camlint_of_coqint n, typ ty)
  | Eparen (e1, ty1, ty2) -> Paren(texpr e1, typ ty1, typ ty2)

and builtin tyargs el ty = function
  | AST.EF_external(name, sg) -> Extern (camlstring_of_coqstring name, typlist tyargs, mapexprlist texpr el)
  | EF_builtin(name, sg) -> Builtin (camlstring_of_coqstring name, typlist tyargs, mapexprlist texpr el, typ ty)
  | EF_vload chunk -> Volatile_load (name_of_chunk chunk, typlist tyargs, mapexprlist texpr el)
  | EF_vstore chunk -> Volatile_store (name_of_chunk chunk, typlist tyargs, mapexprlist texpr el)
  | EF_malloc -> Malloc(typlist tyargs, mapexprlist texpr el)
  | EF_free -> Free(typlist tyargs, mapexprlist texpr el)
  | EF_memcpy(sz, al) -> Memcpy(Z.to_int sz, Z.to_int al,typlist tyargs, mapexprlist texpr el)
  | EF_annot(text, targs) -> Annot (camlstring_of_coqstring text, typlist tyargs, mapexprlist texpr el)
  | EF_annot_val(text, targ) -> Annot_val (camlstring_of_coqstring text, typlist tyargs, mapexprlist texpr el)
  | EF_inline_asm(text, sg, clob) -> Inline_asm (camlstring_of_coqstring text, typlist tyargs, mapexprlist texpr el)
  | EF_debug(kind, text, targs) -> Debug(P.to_int kind, extern_atom text, typlist tyargs, mapexprlist texpr el)

let dolst = ref []

let rec tstmt = function
  | Sskip -> Skip
(*
  | Sset(id, e2) -> Set (temp_name id, texpr e2)
  | Sbuiltin(None, ef, tyargs, el) -> builtin tyargs el ef
  | Sbuiltin(Some id, ef, tyargs, el) -> Set(extern_atom id, builtin tyargs el ef)
*)
  | Sdo(Ecall(e1, el, ty)) -> Call(texpr e1, mapexprlist texpr el, typ ty)
  | Sdo(Eassign(e1, e2, ty)) -> Assign(texpr e1, texpr e2, typ ty)
  | Sdo _ as err -> dolst := err :: !dolst; failwith "Sdo _"
  | Ssequence(Sskip, s2) -> tstmt s2
  | Ssequence(s1, Sskip) -> tstmt s1
  | Ssequence(s1, s2) -> Sequence(tstmt s1, tstmt s2)
  | Sifthenelse(e, s1, s2) -> Ifthenelse(texpr e, tstmt s1, tstmt s2)
  | Swhile(e1, s1) -> While (texpr e1, tstmt s1)
  | Sdowhile(e1, s1) -> While (texpr e1, tstmt s1)
  | Sfor(s1, e2, s3, s4) -> For(tstmt s1, texpr e2, tstmt s3, tstmt s4)
  | Sbreak -> Break
  | Scontinue -> Continue
  | Sswitch(e, cases) -> Switch(texpr e, tcases cases)
  | Sreturn None -> Return Void
  | Sreturn (Some e) -> Return(texpr e)
  | Slabel(lbl, s1) -> Label(extern_atom lbl, tstmt s1)
  | Sgoto lbl -> Goto(extern_atom lbl)

and tcases = function
  | LSnil -> []
  | LScons(None, s, rem) -> Default(tstmt s) :: tcases rem
  | LScons(Some lbl, s, rem) -> Case(Z.to_string lbl, tstmt s) :: tcases rem

let faillst = ref []
let discreplst = ref []
let errlst = ref []

let rec typcmp ctypes (key1, attr1, lst1) (key2, attr2, lst2) =
  let match1 = function
    | (Tstruc(exp1,a1), Tstruc(exp2,a2)) -> (exp1=exp2 && a1=a2) || typcmp ctypes (Hashtbl.find ctypes exp1) (Hashtbl.find ctypes exp2)
    | (Tuni(exp1,a1), Tuni(exp2,a2)) -> exp1=exp2 || typcmp ctypes (Hashtbl.find ctypes exp1) (Hashtbl.find ctypes exp2)
    | (_,_) -> false in
  match1 (key1, key2)

let trans_program ctypes cvars cfun cext prog fmt =
  List.iter (function
    | Composite(id, su, m, a) -> let key = extern_atom id in
      Format.fprintf fmt "%s %s;@ " (PrintCsyntax.struct_or_union su) key) prog.prog_types;
  List.iter (function
    | Composite(id, su, m, a) -> let key = extern_atom id in
      Format.fprintf fmt "@[<v 2>%s %s%s {" (PrintCsyntax.struct_or_union su) key (PrintCsyntax.attributes a);
      List.iter
	(fun (fid, fty) ->
	  Format.fprintf fmt "@ %s;" (PrintCsyntax.name_cdecl (extern_atom fid) fty))
	m;
      Format.fprintf fmt "@;<0 -2>};@]@ @ ";
      
      let lst = List.map (fun (fid, fty) -> (extern_atom fid,typ fty)) m in
      let contents = (struct_or_union key su, attributes a, lst) in
      if Hashtbl.mem ctypes key then
           begin
           let prev = Hashtbl.find ctypes key in
           if not (typcmp ctypes prev contents) then
	       begin
	       discreplst := (prev, contents) :: !discreplst;
	       failwith (key^": type redeclaration error")
	       end
	   end
      else
           Hashtbl.add ctypes key contents) prog.prog_types;
  List.iter (fun (id, gd) -> let key = extern_atom id in match gd with
    | AST.Gfun (External(ef, args, res, cconv)) ->
        Format.fprintf fmt "extern %s;@ @ "
                (PrintCsyntax.name_cdecl (extern_atom id) (Tfunction(args, res, cconv)));
        let contents = (builtin args Enil Tvoid ef, typ res, callconv cconv) in
        if (Hashtbl.mem cext key) then assert(Hashtbl.find cext key = contents)
        else Hashtbl.add cext key contents
    | Gfun (Internal f) ->
	  PrintCsyntax.print_function fmt id f;
          assert(Hashtbl.mem ctypes key == false);
          Hashtbl.add cfun key (
	  callconv f.fn_callconv, 
	  List.map (fun (id,ty) -> (extern_atom id, typ ty)) f.fn_params,
          List.map (fun (id, ty) -> (extern_atom id, typ ty)) f.fn_vars,
          tstmt f.fn_body, rtyp f.fn_return)
    | Gvar v -> PrintCsyntax.print_globvar fmt id v; let tinit = List.map (function
	   | AST.Init_space n -> Space (Int32.to_int (camlint_of_coqint n))
	   | Init_int8 n -> Char (Int32.to_int (camlint_of_coqint n))
	   | Init_int16 n -> Short (Int32.to_int (camlint_of_coqint n))
	   | Init_int32 n -> Long (camlint_of_coqint n)
	   | Init_int64 n -> LongLong (camlint64_of_coqint n)
	   | Init_float32 n -> Float (coqsingle n)
	   | Init_float64 n -> Double (coqfloat n)
	   | Init_addrof (id, m) -> Addrof(extern_atom id, camlint_of_coqint m)) v.gvar_init in
           assert(Hashtbl.mem ctypes key == false);
	   Hashtbl.add cvars key (v.gvar_readonly, tinit, typ v.gvar_info)) prog.prog_defs

(* Precedences and associativity -- like those of C *)

type flags =
  | Fnone
  | Fpure
  | Finline
  | Fmemcpy
  | Fnostack
  | Fhardware
  | Fspecialised
  | Fopt2

type fmt =
  | FmtNone
  | FmtLhs
  | FmtRhs
  | FmtPrintf

type intfn = trans * (string * trans) list * (string * trans) list * trans * trans

and fnhash = {
  extern:(string,intfn) Hashtbl.t;
  intern:(string,intfn) Hashtbl.t;
  gvar:(string, bool * trans list * trans) Hashtbl.t;
  modes:(string,AST.memory_chunk) Hashtbl.t;
  extratasks:(string,intfn) Hashtbl.t;
  buffers:(string,int32*Buffer.t) Hashtbl.t;
  memories:(string,Buffer.t) Hashtbl.t;
  used:(string,unit) Hashtbl.t;
  depend:(string,string) Hashtbl.t;
  subs:(string*trans) list;
  buflst:(string*string) list ref;
  geval:(string*int32, trans*trans) Hashtbl.t;
  unopt:(string,trans list) Hashtbl.t;
}

and print = {
  out: Buffer.t;
  membuf: Buffer.t;
  indent: string;
  blocklbl: int ref;
  stem: string;
  nest: string list;
  hashdata:fnhash;
  prec': int;
  prec1: int;
  prec2: int;
  fmt:fmt;
  taskcnt: int ref;
  top: bool;
  initoff: int ref;
  initfunc: string;
  sig_res: trans option;
  boolcontext: bool;
  exnbuf: Buffer.t;
  fixed: bool;
  topfunc: string;
  hardware: bool;
  pure: bool;
  assertions: ((trans*trans)*(trans*trans)) list;
  chk: formatter
}

type associativity = LtoR | RtoL | NA

let rec precedence = function
  | Var _ -> (16, NA)
  | Const_int _ -> (16, NA)
  | Const_float _ -> (16, NA)
  | Const_single _ -> (16, NA)
  | Const_long _ -> (16, NA)
  | Tnotbool _|Tnotint _|Tneg _|Tabs _ -> (15, RtoL)
  | Tmul _|Tdiv _|Tmod _ -> (13, LtoR)
  | Taddlst _ -> (12, LtoR)
  | Tadd _|Tsub _ -> (12, LtoR)
  | Tshl _|Tshr _ -> (11, LtoR)
  | Teq _|Tne _ |Tlt _|Tgt _|Tle _|Tge _ -> (10, LtoR)
  | Tand _ -> (8, LtoR)
  | Txor _ -> (7, LtoR)
  | Tor _ -> (6, LtoR)
  | _ -> (1,NA)

(* Naming operators *)

let othlst = ref []

let myfail str err =
  faillst := err :: !faillst;
  failwith str

let name_of_binop = function
  | Tadd _ -> "+@"
  | Tsub _ -> "-@"
  | Tmul _ -> "*@"
  | Tdiv _ -> "/@"
  | Tmod _ -> "%@"
  | Tand _ -> "&@"
  | Tor _ -> "|@"
  | Txor _ -> "^@"
  | Tshl _ -> "<<@"
  | Tshr _ -> ">>@"
  | Teq _ -> " = "
  | Tne _ -> " <> "
  | Tlt _ -> " < "
  | Tle _ -> " <= "
  | Tgt _-> " > "
  | Tge _ -> " >= "
  | oth -> myfail "name_of_binop" oth

let rec name_of_type = function
  | Tbool a -> "bool"
  | Schar a -> "signed char"
  | Uchar a -> "unsigned char"
  | Sshort a -> "signed short"
  | Ushort a -> "unsigned short"
  | Sint a -> "signed int"
  | Uint a -> "unsigned int"
  | Slong a -> "signed long"
  | Ulong a -> "unsigned long"
  | Tfloat a -> "float"
  | Tdouble a -> "float"
  | Tptr(t, a) -> name_of_type t^" *"
  | Tstruc(s, a) -> "struct_"^s
  | Tuni(s, a) -> "uni_"^s
  | Void -> "unit"
  | Array (typ, len, a) -> name_of_type typ^" array"
  | oth -> othlst := oth :: !othlst; myfail "name_of_type" oth

let rec init_of_type = function
  | Tbool a -> "false"
  | Schar a -> "'0'"
  | Uchar a -> "'0'"
  | Sshort a -> "0"
  | Ushort a -> "0"
  | Sint a -> "0"
  | Uint a -> "0"
  | Slong a -> "0l"
  | Ulong a -> "0l"
  | Tfloat a -> "0f"
  | Tdouble a -> "0f"
  | Tptr (Tptr (Schar a, a'), a'') -> "\"\""
  | Tptr (Tstruc (s,a), a') -> "ref ()"
  | Tptr (Tuni (s,a), a') -> "ref ()"
  | Tptr (Tdouble a, a') -> "ref 0.0"
  | Tptr (Schar a, a') -> "ref ' '"
  | Tptr (Sshort a, a') -> "ref 0"
  | Tptr (Void, a') -> "ref ()"
  | Tptr (oth, a) -> "ref ("^init_of_type oth^")"
  | Tstruc (s, a) -> "struc_"^s
  | Tuni (u, a) -> "uni_"^u
  | Array (typ, len, a) -> "Array.make "^Int32.to_string len^ (init_of_type typ)
  | Void -> "()"
  | oth -> othlst := oth :: !othlst; myfail "init_of_type" oth

let rec format_cnv str =
  if str = "" then "" else
    if str.[0] <> '%' then
      String.sub str 0 1^format_cnv (String.sub str 1 (String.length str - 1))
    else
      match str.[1] with
       | 'd' -> "%ld"^format_cnv (String.sub str 2 (String.length str - 2))
       | 'u' -> "%lu"^format_cnv (String.sub str 2 (String.length str - 2))
       | 'l' -> "%L"^format_cnv (String.sub str 2 (String.length str - 2))
       | _ -> "%"^format_cnv (String.sub str 1 (String.length str - 1))

(* Expressions *)

(* Types *)

let rec init_length = function
  | hd::tl -> let len = match hd with
    | Char i -> 1l
    | Short i -> 2l
    | Long i -> 4l
    | LongLong i -> 8l
    | Float f -> 4l
    | Double f -> 8l
    | Space n -> Int32.of_int n
    | Addrof (off, id) -> 4l
    | _ -> 0l in Int32.add len (init_length tl)
  | [] -> 0l

(*
let init_length id = function
  | Qinit lst -> init_length lst
  | Qinitstr str -> Int32.of_int (String.length str)
  | Qglobvar (_,_,_, Qinit lst) -> init_length lst
  | _ -> 0l

let print_sig out sg =
  List.iter (fun t -> bprintf out "`%s -> " (name_of_type t)) sg.sig_args;
  match sg.sig_res with
  | None -> bprintf out "void"
  | Some ty -> bprintf out "`%s" (name_of_type ty)
*)

type dbg = 
  | Test
  | False
  | True

let stream' = function
    | "__stdoutp" -> "stdout"
    | "__stderrp" -> "stderr"
    | oth -> oth

let print_pointer_hook
   : (formatter -> Values.block * Integers.Int.int -> unit) ref
   = ref (fun p (b, ofs) -> ())

let print_typed_value out v ty =
  match v with
  | Const_int(n, Uint a) -> bprintf out "%luU" n
  | Const_int (n, _) -> bprintf out "%ld" n
  | Const_float (f, _) -> bprintf out "%F" f
  | Const_single (f, _) -> bprintf out "%Ff" f
  | Const_long (n, Ulong _) -> bprintf out "%LuLLU" n
  | Const_long (n, _) -> bprintf out "%LdLL" n
  | Const_ptr (b, _) -> bprintf out "%LdLL" b
  | _ -> bprintf out "<undef>"

(* Statements *)
let rec print_stmt p _ = function
  | Debug(n,str,args,sg) -> Printf.bprintf p.out "(*skip*)"
  | Set(lhs, rhs) -> Printf.bprintf p.out "%s := %a;" lhs (print_expr p) rhs; 
  | Field (Var (lhs, Tstruc _), rhs, ty) -> Printf.bprintf p.out "%s.%s" lhs rhs;
  | Sizeof (ty, Uint a) -> Printf.bprintf p.out "sizeof(%s)" (name_of_type ty);
  | Call(Valof(Var(id, sg), ty), modargs, ty') ->
      print_endline ("Call("^p.stem^"): "^id);
      Printf.bprintf p.out "task_%s" id;
      List.iter (fun itm -> Printf.bprintf p.out " (%a)" (print_expr p) itm) modargs;
      if modargs <> [] then Printf.bprintf p.out ";\n%s" p.indent else Printf.bprintf p.out " ();\n%s" p.indent;
      Hashtbl.replace p.hashdata.used id ();
      if p.stem <> id then Hashtbl.add p.hashdata.depend p.stem id;
      if p.stem <> id && Hashtbl.mem p.hashdata.intern id then
          begin
          print_endline ("Local call: "^id);
          Hashtbl.add p.hashdata.extratasks id (Hashtbl.find p.hashdata.intern id);
          end;
  | Valof(l, _) -> Printf.bprintf p.out " (%a)" (print_expr p) l
  | Val(v, ty) -> print_typed_value p.out v ty
  | Comma(a1, a2, _) -> Printf.bprintf p.out "%a, %a" (print_expr p) a1 (print_expr p) a2
  | Taddrof (vexp, typ) -> Printf.bprintf p.out "ref %a" (print_expr p) vexp;
     
  | Const_int (n, Sint a) -> Printf.bprintf p.out "%ld" n;
     
  | Teq (lft, rght, Sint a) -> Printf.bprintf p.out "%a = %a" (print_expr p) lft (print_expr p) rght;
  | Tne (lft, rght, Sint a) -> Printf.bprintf p.out "%a <> %a" (print_expr p) lft (print_expr p) rght;
  | Tgt (lft, rght, Sint a) -> Printf.bprintf p.out "%a > %a" (print_expr p) lft (print_expr p) rght;
  | Tge (lft, rght, Sint a) -> Printf.bprintf p.out "%a >= %a" (print_expr p) lft (print_expr p) rght;
  | Tlt (lft, rght, Sint a) -> Printf.bprintf p.out "%a < %a" (print_expr p) lft (print_expr p) rght;
  | Tle (lft, rght, Sint a) -> Printf.bprintf p.out "%a <= %a" (print_expr p) lft (print_expr p) rght;
     
  | Tadd (lft, rght, typ) -> Printf.bprintf p.out "%a + %a" (print_expr p) lft (print_expr p) rght;
  | Tsub (lft, rght, typ) -> Printf.bprintf p.out "%a - %a" (print_expr p) lft (print_expr p) rght;
  | Tmul (lft, rght, typ) -> Printf.bprintf p.out "%a * %a" (print_expr p) lft (print_expr p) rght;
  | Tdiv (lft, rght, typ) -> Printf.bprintf p.out "%a / %a" (print_expr p) lft (print_expr p) rght;
  | Tshr (lft, rght, typ) -> Printf.bprintf p.out "%a lsr %a" (print_expr p) lft (print_expr p) rght;
  | Tnotbool (lft, typ) -> Printf.bprintf p.out "!%a" (print_expr p) lft
  | Tneg (lft, typ) -> Printf.bprintf p.out "-%a" (print_expr p) lft
  | Taddlst (typ, lst) -> let delim = ref ' ' in 
      List.iter (fun itm -> Printf.bprintf p.out "%c%a" !delim (print_expr p) itm; delim := '+') lst
  | Var (nam, Array (Schar a, len, a')) when String.length nam > 12 && String.sub nam 0 12 = "__stringlit_" ->
      if Hashtbl.mem p.hashdata.gvar nam then
      (let (readonly, init, info) = Hashtbl.find p.hashdata.gvar nam in
      Printf.bprintf p.out "\"";
      List.iter (function Char itm -> Printf.bprintf p.out "%c" (char_of_int itm) | _ -> failwith "init") init;
      Printf.bprintf p.out "\"")
      else Printf.bprintf p.out "\"%s\"" (String.escaped nam);
  | Var (nam, typ) -> Printf.bprintf p.out "%s" nam;
  | Const_float(arg, Tdouble a) -> Printf.bprintf p.out "%f" arg
  | Void -> Printf.bprintf p.out "()"
  | Ifthenelse (condition,
    thenlst,
    elselst) ->
      Printf.bprintf p.out "if %a then " (print_expr p) condition;
      Printf.bprintf p.out " (%a)" (print_stmt p) thenlst;
      Printf.bprintf p.out " else ";
      Printf.bprintf p.out " (%a)" (print_stmt p) elselst
  | Assign (dest, expr, ty) -> Printf.bprintf p.out "%a = %a" (print_expr p) dest (print_expr p) expr
  | Cast (temp, typ) -> Printf.bprintf p.out "Cast(%a, %s)" (print_expr p) temp (name_of_type typ)
  | For (dst, expr, arg3, looplst) ->
      Printf.bprintf p.out "For(%a, %a, %a, %a)" (print_expr p) dst (print_expr p) expr (print_expr p) arg3 (print_stmt p) looplst
  | While (condition, looplst) -> Printf.bprintf p.out "while %a do %a done" (print_expr p) condition (print_stmt p) looplst
  | Return expr -> Printf.bprintf p.out "rslt_%s := %a; raise Block_%s;" p.stem (print_expr p) expr p.stem
  | Field (Deref (ptr, Tstruc (info,a'')), fld, typ) -> Printf.bprintf p.out "%a->%s" (print_expr p) ptr fld
  | Field (exp, nam, typ) -> Printf.bprintf p.out "%a->%s" (print_expr p) exp nam
  | Deref (ptr, typ) -> Printf.bprintf p.out "!%a" (print_expr p) ptr
  | Switch (exp, caselst) -> Printf.bprintf p.out "match %a with %a" (print_expr p) exp (print_stmt_list p) caselst
  | Case (itm, stmtlst) -> Printf.bprintf p.out "| %s -> %a" itm (print_stmt p) stmtlst
  | Default stmtlst -> Printf.bprintf p.out "| _ -> %a" (print_stmt p) stmtlst
  | Break -> Printf.bprintf p.out "raise Break_%s" p.stem
  | Continue -> Printf.bprintf p.out "raise Continue_%s" p.stem
  | Goto dest -> Printf.bprintf p.out "raise Goto_%s_%s" p.stem dest
  | Label (dest,lst) -> Printf.bprintf p.out "with Goto_%s_%s -> %a" p.stem dest (print_stmt p) lst
  | Sequence (s1, s2) -> Printf.bprintf p.out "%a;%a" (print_stmt p) s1 (print_stmt p) s2
  | Const_int (n, Void) -> Printf.bprintf p.out "%ld" n
  | err -> errlst := err :: !errlst; myfail "Other" err

and expr p out (prec, e) =
  let (prec', assoc) = precedence e in
  let (prec1, prec2) =
    if assoc = LtoR
    then (prec', prec' + 1)
    else (prec' + 1, prec') in
  if prec' < prec
  then Printf.bprintf out "("
  else Printf.bprintf out "";
  print_stmt {p with prec'=prec'; prec1=prec1; prec2=prec2} p.out e;
  if prec' < prec then Printf.bprintf out ")"

and print_expr p out e = expr p out (0, e)

and print_expr_list p out (first, rl) =
  match rl with
  | [] -> ()
  | r :: rl ->
      if not first then Printf.bprintf out ", ";
      expr p out (2, r);
      print_expr_list p out (false, rl)

and print_stmt_list p out = function
  | [] -> ()
  | r :: rl ->
      Printf.bprintf out ";\n\t";
      print_stmt p out r;
      print_stmt_list p out rl

(* Functions *)

and print_func p fn_id (callconv, fn_params, fn_vars, fn_body, fn_return) =
  assert(p.stem=fn_id);
  Printf.bprintf p.out "type vars_%s = {\n" p.stem;
  List.iter  (fun (k,t) -> Printf.bprintf p.out "_%s_%s: %s ref;\n" p.stem k (name_of_type t)) (fn_params @ fn_vars);
(*
  (match fn_sig.sig_res with
    | Some t -> Printf.bprintf p.out "_%s_res: %s ref;" p.stem (name_of_type t)
    | None -> Printf.bprintf p.out "_%s_res: unit ref;" p.stem);
*)
  Printf.bprintf p.out "}\n\n";
  Printf.bprintf p.out "type dbg_%s = {\n" p.stem;
  List.iter  (fun (k,t) -> Printf.bprintf p.out "dbg_%s_%s: %s;\n" p.stem k (name_of_type t)) (fn_params @ fn_vars);
(*
  (match fn_sig.sig_res with
    | Some t -> Printf.bprintf p.out "dbg_%s_res: %s;" p.stem (name_of_type t)
    | None -> Printf.bprintf p.out "dbg_%s_res: unit;" p.stem);
*)
  Printf.bprintf p.out "}\n\n";
  Printf.bprintf p.out "let copy_%s src = {\n" p.stem;
  List.iter  (fun (k,t) -> Printf.bprintf p.out "dbg_%s_%s = !(src._%s_%s);\n" p.stem k p.stem k) (fn_params @ fn_vars);
  Printf.bprintf p.out "dbg_%s_res = !(src._%s_res);\n" p.stem p.stem;
  Printf.bprintf p.out "}\n\n";
  Printf.bprintf p.out "let (dbg_%s_lst:(string*dbg_%s*algebraic array) list ref) = ref []\n\n" p.stem p.stem;
  Printf.bprintf p.out "let r_%s = {\n" p.stem;
  List.iter  (fun (k,t) -> Printf.bprintf p.out "_%s_%s = ref %s;\n" p.stem k (init_of_type t)) (fn_params @ fn_vars);
(*
  (match fn_sig.sig_res with
    | Some t -> Printf.bprintf p.out "_%s_res = ref %s;\n" p.stem (init_of_type t)
    | None -> Printf.bprintf p.out "_%s_res = ref ();\n" p.stem);
*)
  Printf.bprintf p.out "}\n\n";
  Printf.bprintf p.out "let task_%s" p.stem;
  if fn_params <> [] then
      List.iter (fun (k,ty) -> Printf.bprintf p.out " (_%s:%s)" k (name_of_type ty)) fn_params
  else
      Printf.bprintf p.out " ()";
(*
  (match fn_sig.sig_res with
    | Some t -> Printf.bprintf p.out ": %s =\n" (name_of_type t)
    | None -> Printf.bprintf p.out ": unit =\n");
*)
  List.iter  (fun (k,t) -> Printf.bprintf p.out "r_%s._%s_%s := _%s;\n" p.stem p.stem k k) fn_params;
  Printf.bprintf p.out "begin\ndbg_%s_lst := [];\n\n" p.stem;
  Printf.bprintf p.out "%stry (* %s *)\n%s" p.indent p.stem p.indent;
  Printf.bprintf p.exnbuf "exception Block_%s\n" p.stem;
  print_stmt {p with indent="  "^p.indent (*; sig_res=fn_sig.sig_res *)} p.out fn_body;
  Printf.bprintf p.out "\n%swith Block_%s -> ()\nend;\n" p.indent p.stem;
  Printf.bprintf p.out "!(r_%s._%s_res)\n (* task_%s *)\n\n" p.stem p.stem p.stem

let rec print_varlist p (vars, first) =
  match vars with
  | [] -> ()
  | v1 :: vl ->
      if not first then Printf.bprintf p.out ", ";
      Printf.bprintf p.out "%s" (v1);
      print_varlist p (vl, false)

let rec print_init_data_list p = function
  | [] -> ()
  | [item] -> print_stmt p p.out item
  | item::rest ->
      (print_stmt p p.out item;
       Printf.bprintf p.out ",";
       print_init_data_list p rest)

let attributes = function
  | Void -> ""
  | Tvolatile -> "volatile"
  | Alignas n -> sprintf " _Alignas(%Ld)" (Int64.shift_left 1L (Int32.to_int n))
  | Tvolatile_alignas n -> sprintf " _Alignas(%Ld) volatile" (Int64.shift_left 1L (Int32.to_int n))
  | oth -> "attribute invalid"

let attributes_space a =
  let s = attributes a in
  if String.length s = 0 then s else s ^ " "

let name_optid id =
  if id = "" then "" else " " ^ id

let rec name_cdecl id ty =
  match ty with
  | Void -> "void" ^ name_optid id
  | Schar a -> "signed char" ^ attributes a ^ name_optid id
  | Uchar a -> "unsigned char" ^ attributes a ^ name_optid id
  | Sshort a -> "signed short" ^ attributes a ^ name_optid id
  | Ushort a -> "unsigned short" ^ attributes a ^ name_optid id
  | Sint a -> "signed int" ^ attributes a ^ name_optid id
  | Uint a -> "unsigned int" ^ attributes a ^ name_optid id
  | Tfloat a -> "float" ^ attributes a ^ name_optid id
  | Tdouble a -> "double" ^ attributes a ^ name_optid id
  | Slong a -> "signed long" ^ attributes a ^ name_optid id
  | Ulong a -> "unsigned long" ^ attributes a ^ name_optid id
  | Tptr(t, a) ->
      let id' =
        match t with
        | Tfunc _ | Array _ -> sprintf "(*%s%s)" (attributes_space a) id
        | _                      -> sprintf "*%s%s" (attributes_space a) id in
      name_cdecl id' t
  | Array(t, n, a) -> name_cdecl (sprintf "%s[%ld]" id n) t
  | Tfunc(args, res, cconv) ->
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b id;
      Buffer.add_char b '(';
      let rec add_args first = function
      | [] ->
          let varargs = match cconv with Tcallconv(true,_,_) -> true | _ -> false in
          if first then
            Buffer.add_string b
               (if varargs then "..." else "void")
          else if varargs then
            Buffer.add_string b ", ..."
          else
            ()
      | t1 :: tl ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_cdecl "" t1);
          add_args false tl in
      (match cconv with Tcallconv(_, true, _) -> () | _ -> add_args true args);
      Buffer.add_char b ')';
      name_cdecl (Buffer.contents b) res
  | Tstruc(name, a) -> "struct " ^ name ^ attributes a ^ name_optid id
  | Tuni(name, a) -> "union " ^ name ^ attributes a ^ name_optid id
  | oth -> "invalid_type_name"

let name_function_parameters fun_name params cconv =
  let varargs = match cconv with Tcallconv(true,_,_) -> true | _ -> false in
  let b = Buffer.create 20 in
  Buffer.add_string b fun_name;
  Buffer.add_char b '(';
  begin match params with
  | [] ->
      Buffer.add_string b (if varargs then "..." else "void")
  | _ ->
      let rec add_params first = function
      | [] ->
          if varargs then Buffer.add_string b "..."
      | (id, ty) :: rem ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_cdecl id ty);
          add_params false rem in
      add_params true params
  end;
  Buffer.add_char b ')';
  Buffer.contents b

let cname_binop = function
  | Tadd _ -> "+@"
  | Tsub _ -> "-@"
  | Tmul _ -> "*@"
  | Tdiv _ -> "/@"
  | Tmod _ -> "%@"
  | Tand _ -> "&@"
  | Tor _ -> "|@"
  | Txor _ -> "^@"
  | Tshl _ -> "<<@"
  | Tshr _ -> ">>@"
  | Teq _ -> " = "
  | Tne _ -> " <> "
  | Tlt _ -> " < "
  | Tle _ -> " <= "
  | Tgt _-> " > "
  | Tge _ -> " >= "
  | oth -> myfail "name_of_binop" oth

let cexprlst = ref []
let vallst = ref []

let print_pointer_hook
   : (formatter -> Values.block * Integers.Int.int -> unit) ref
   = ref (fun p (b, ofs) -> ())

let rec cexpr p (prec, e) =
  let (prec', assoc) = precedence e in
  let (prec1, prec2) =
    if assoc = LtoR
    then (prec', prec' + 1)
    else (prec' + 1, prec') in
  if prec' < prec
  then fprintf p "@[<hov 2>("
  else fprintf p "@[<hov 2>";
  begin match e with
  | Var(id, _) ->
      fprintf p "%s" id
  | Deref(a1, _) ->
      fprintf p "*%a" cexpr (prec', a1)
  | Field(a1, f, _) ->
      fprintf p "%a.%s" cexpr (prec', a1) f
  | Const_int(n, Uint _) ->
      fprintf p "%luU" n
  | Const_int(n, _) ->
      fprintf p "%ld" n
  | Const_float(f, _) ->
      fprintf p "%F" f
  | Const_single(f, _) ->
      fprintf p "%Ff" f
  | Const_long(n, Ulong _) ->
      fprintf p "%LuLLU" n
  | Const_long(n, _) ->
      fprintf p "%LdLL" n
  | Tabs(a1, _) ->
      fprintf p "__builtin_fabs(%a)" cexpr (2, a1)
  | Tneg(a1, _) ->
      fprintf p "-%a" cexpr (prec', a1)
  | Tnotint(a1, _) ->
      fprintf p "~%a" cexpr (prec', a1)
  | Tnotbool(a1, _) ->
      fprintf p "!%a" cexpr (prec', a1)
  | Taddrof(a1, _) ->
      fprintf p "&%a" cexpr (prec', a1)
  | Tadd(a1, a2, _) ->
      fprintf p "%a@ %s %a"
                 cexpr (prec1, a1) (cname_binop e) cexpr (prec2, a2)
  | Cast(a1, ty) ->
      fprintf p "(%s) %a" (name_cdecl "" ty) cexpr (prec', a1)
  | Sizeof(ty, _) ->
      fprintf p "sizeof(%s)" (name_cdecl "" ty)
  | Alignof(ty, _) ->
      fprintf p "__alignof__(%s)" (name_cdecl "" ty)
  | Call(e1, el, ty) ->
      fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@]);@]"
                print_cexpr e1
                print_cexpr_list (true, el)
  | Valof(l, _) -> cexpr p (prec, l)
  | Val(v, ty) ->
      vallst := e :: !vallst;
      let b = Buffer.create 256 in print_typed_value b v ty;
      fprintf p "%s" (Buffer.contents b)
  | Comma(a1, a2, _) ->
      fprintf p "%a,@ %a" cexpr (prec1, a1) cexpr (prec2, a2)
  | oth -> cexprlst := oth :: !cexprlst; failwith "cexpr"
  end;
  if prec' < prec then fprintf p ")@]" else fprintf p "@]"

and print_cexpr p e = cexpr p (0, e)

and print_cexpr_list p (first, rl) =
  match rl with
  | [] -> ()
  | r :: rl ->
      if not first then fprintf p ",@ ";
      cexpr p (2, r);
      print_cexpr_list p (false, rl)

let rec print_cstmt (p:formatter) s =
  match s with
  | Assign(e1, e2, ty) ->
      fprintf p "@[<hv 2>%a =@ %a;@]" print_cexpr e1 print_cexpr e2
  | Call(e1, el, ty) ->
      fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@]);@]"
                print_cexpr e1
                print_cexpr_list (true, el)
  | Set(id, Call(e1, el, ty)) ->
      fprintf p "@[<hv 2>%s =@ %a@,(@[<hov 0>%a@]);@]"
                id
                print_cexpr e1
                print_cexpr_list (true, el)
  | Builtin(ef, tyargs, el, ty) ->
      fprintf p "@[<hv 2>builtin %s@,(@[<hov 0>%a@]);@]"
                ef
                print_cexpr_list (true, el)
  | Set(id, Builtin(ef, tyargs, el, ty)) ->
      fprintf p "@[<hv 2>%s =@ builtin %s@,(@[<hov 0>%a@]);@]"
                id
                ef
                print_cexpr_list (true, el)
  | Set(id, e2) ->
      fprintf p "@[<hv 2>%s =@ %a;@]" id print_cexpr e2
  | Sequence(Skip, s2) -> print_cstmt p s2
  | Sequence(s1, Skip) -> print_cstmt p s1
  | Sequence(s1, s2) -> fprintf p "%a@ %a" print_cstmt s1 print_cstmt s2
  | Ifthenelse(e, s1, Skip) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>}@]"
              print_cexpr e
              print_cstmt s1
  | Ifthenelse(e, Skip, s2) ->
      fprintf p "@[<v 2>if (! %a) {@ %a@;<0 -2>}@]"
              cexpr (15, e)
              print_cstmt s2
  | Ifthenelse(e, s1, s2) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_cexpr e
              print_cstmt s1
              print_cstmt s2
  | While(e1, s1) ->
      fprintf p "@[<v 2>while (1) {@ %a@;<0 -2>}@]"
              print_cstmt s1
  | For(s1, s2, s3, s4) ->
      fprintf p "@[<v 2>for (@[<hv 0>;@ 1;@ %a) {@]@ %a@;<0 -2>}@]"
              print_cstmt_for s2
              print_cstmt s1
  | Break ->
      fprintf p "break;"
  | Continue ->
      fprintf p "continue;"
  | Switch(e, cases) ->
      fprintf p "@[<v 2>switch (%a) {@ %a@;<0 -2>}@]"
              print_cexpr e
              print_cases cases
  | Return Void ->
      fprintf p "return;"
  | Return e ->
      fprintf p "return %a;" print_cexpr e
  | Label(lbl, s1) ->
      fprintf p "%s:@ %a" lbl print_cstmt s1
  | Goto lbl ->
      fprintf p "goto %s;" lbl
  | oth -> othlst := oth :: !othlst; failwith "print_cstmt"

and print_cases p cases =
  match cases with
  | [] -> ()
  | Default Skip :: rem ->
      fprintf p "default:@ %a"
              print_cases rem
  | Default s :: rem ->
      fprintf p "@[<v 2>default:@ %a@]@ %a"
              print_cstmt s
              print_cases rem
  | Case(lbl, Skip) :: rem ->
      fprintf p "case %s:@ %a"
              lbl
              print_cases rem
  | Case(lbl, s) :: rem ->
      fprintf p "@[<v 2>case %s:@ %a@]@ %a"
              lbl
              print_cstmt s
              print_cases rem
  | oth -> failwith "cases error"

and print_cstmt_for p s =
  match s with
  | Assign(e1, e2, ty) ->
      fprintf p "%a = %a" print_cexpr e1 print_cexpr e2
  | Sequence(s1, s2) ->
      fprintf p "%a, %a" print_cstmt_for s1 print_cstmt_for s2
  | Call(e1, el, ty) ->
      fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@])@]"
                print_cexpr e1
                print_cexpr_list (true, el)
  | Set(id, Call(e1, el, ty)) ->
      fprintf p "@[<hv 2>%s =@ %a@,(@[<hov 0>%a@])@]"
                id
                print_cexpr e1
                print_cexpr_list (true, el)
  | Builtin(ef, tyargs, el, ty) ->
      fprintf p "@[<hv 2>builtin %s@,(@[<hov 0>%a@]);@]"
                ef
                print_cexpr_list (true, el)
  | Set(id, Builtin(ef, tyargs, el, ty)) ->
      fprintf p "@[<hv 2>%s =@ builtin %s@,(@[<hov 0>%a@]);@]"
                id
                ef
                print_cexpr_list (true, el)
  | Set(id, e2) ->
      fprintf p "%s = %a" id print_cexpr e2
  | _ ->
      fprintf p "({ %a })" print_cstmt s

let dumpcombined_exn hashdata outfile topfunc fmt =
  let fout = open_out outfile in
  output_string fout "let ( ~-@ ) : int32 -> int32 = Int32.neg\n";
  output_string fout "let ( +@ ) : int32 -> int32 -> int32 = Int32.add\n";
  output_string fout "let ( -@ ) : int32 -> int32 -> int32 = Int32.sub\n";
  output_string fout "let ( *@ ) : int32 -> int32 -> int32 = Int32.mul\n";
  output_string fout "let ( /@ ) : int32 -> int32 -> int32 = Int32.div\n";
  output_string fout "let ( %@ ) : int32 -> int32 -> int32 = Int32.rem\n";
  output_string fout "let ( &@ ) : int32 -> int32 -> int32 = Int32.logand\n";
  output_string fout "let ( |@ ) : int32 -> int32 -> int32 = Int32.logor\n";
  output_string fout "let ( ^@ ) : int32 -> int32 -> int32 = Int32.logxor\n";
  output_string fout "let ( <<@ ) : int32 -> int32 -> int32 = fun x y -> Int32.shift_left x (Int32.to_int y)\n";
  output_string fout "let ( >>@ ) : int32 -> int32 -> int32 = fun x y -> Int32.shift_right x (Int32.to_int y)\n";
  output_string fout "let ( ~-@@ ) : int64 -> int64 = Int64.neg\n";
  output_string fout "let ( +@@ ) : int64 -> int64 -> int64 = Int64.add\n";
  output_string fout "let ( -@@ ) : int64 -> int64 -> int64 = Int64.sub\n";
  output_string fout "let ( *@@ ) : int64 -> int64 -> int64 = Int64.mul\n";
  output_string fout "let ( /@@ ) : int64 -> int64 -> int64 = Int64.div\n";
  output_string fout "let ( %@@ ) : int64 -> int64 -> int64 = Int64.rem\n";
  output_string fout "let ( &@@ ) : int64 -> int64 -> int64 = Int64.logand\n";
  output_string fout "let ( |@@ ) : int64 -> int64 -> int64 = Int64.logor\n";
  output_string fout "let ( ^@@ ) : int64 -> int64 -> int64 = Int64.logxor\n";
  output_string fout "let ( <<@@ ) : int64 -> int32 -> int64 = fun x y -> Int64.shift_left x (Int32.to_int y)\n";
  output_string fout "let ( >>@@ ) : int64 -> int32 -> int64 = fun x y -> Int64.shift_right x (Int32.to_int y)\n";
  output_string fout "\n";
  output_string fout "type algebraic = \n";
  output_string fout "| Void\n";
  output_string fout "| Char of int\n";
  output_string fout "| Short of int\n";
  output_string fout "| Int of int32\n";
  output_string fout "| Long of int64\n";
  output_string fout "| Float of int32\n";
  output_string fout "| Double of int64\n";
  output_string fout "| Space of int\n";
  output_string fout "| Addrof of int\n";
  output_string fout "\n";
  output_string fout "let __load_float64 = function\n";
  output_string fout "| Void -> failwith \"Void\"\n";
  output_string fout "| Char int -> failwith \"Char\"\n";
  output_string fout "| Short int -> failwith \"Short\"\n";
  output_string fout "| Int int32 -> failwith \"Int\"\n";
  output_string fout "| Long int64 -> Int64.float_of_bits int64\n";
  output_string fout "| Float int32 -> failwith \"Float\"\n";
  output_string fout "| Double int64 -> Int64.float_of_bits int64\n";
  output_string fout "| Space int -> failwith \"Space\"\n";
  output_string fout "| Addrof int -> failwith \"Addrof\"\n";
  output_string fout "\n";
  output_string fout "let __load_int64 off4 = function\n";
  output_string fout "| Void -> failwith \"Void\"\n";
  output_string fout "| Char int -> failwith \"Char\"\n";
  output_string fout "| Short int -> failwith \"Short\"\n";
  output_string fout "| Int int32 -> (match off4 with Int int32' -> ((Int64.of_int32 int32') <<@@ 32l) |@@ (Int64.of_int32 int32) | _ -> failwith \"load_int64\")\n";
  output_string fout "| Long int64 -> int64\n";
  output_string fout "| Float int32 -> failwith \"Float\"\n";
  output_string fout "| Double int64 -> int64\n";
  output_string fout "| Space int -> failwith \"Space\"\n";
  output_string fout "| Addrof int -> failwith \"Addrof\"\n";
  output_string fout "\n";
  output_string fout "let __load_int32 = function\n";
  output_string fout "| Void -> failwith \"Void\"\n";
  output_string fout "| Char int -> failwith \"Char\"\n";
  output_string fout "| Short int -> failwith \"Short\"\n";
  output_string fout "| Int int32 -> int32\n";
  output_string fout "| Long int64 -> failwith \"Long\"\n";
  output_string fout "| Float int32 -> failwith \"Float\"\n";
  output_string fout "| Double int64 -> failwith \"Double\"\n";
  output_string fout "| Space int -> failwith \"Space\"\n";
  output_string fout "| Addrof int -> failwith \"Addrof\"\n";
  output_string fout "\n";
  output_string fout "let __load_int8 = function\n";
  output_string fout "| Void -> failwith \"Void\"\n";
  output_string fout "| Char int -> int\n";
  output_string fout "| Short int -> failwith \"Short\"\n";
  output_string fout "| Int int32 -> failwith \"Int\"\n";
  output_string fout "| Long int64 -> failwith \"Long\"\n";
  output_string fout "| Float int32 -> failwith \"Float\"\n";
  output_string fout "| Double int64 -> failwith \"Double\"\n";
  output_string fout "| Space int -> failwith \"Space\"\n";
  output_string fout "| Addrof int -> failwith \"Addrof\"\n";
  output_string fout "\n";
  output_string fout "let __load_any32 = function\n";
  output_string fout "| Void -> failwith \"Void\"\n";
  output_string fout "| Char int -> failwith \"Char\"\n";
  output_string fout "| Short int -> failwith \"Short\"\n";
  output_string fout "| Int int32 -> int32\n";
  output_string fout "| Long int64 -> failwith \"Long\"\n";
  output_string fout "| Float int32 -> failwith \"Float\"\n";
  output_string fout "| Double int64 -> failwith \"Double\"\n";
  output_string fout "| Space int -> failwith \"Space\"\n";
  output_string fout "| Addrof int -> failwith \"Addrof\"\n";
  output_string fout "\n";
  output_string fout ("let _load_float64 nam arr adr = __load_float64 arr.(adr)\n") ;
  output_string fout ("let _load_int64 nam arr adr = __load_int64 arr.(adr+4) arr.(adr)\n");
  output_string fout ("let _load_any32 nam arr adr = __load_any32 arr.(adr)\n");
  output_string fout ("let _load_int32 nam arr adr = __load_int32 arr.(adr)\n");
  output_string fout ("let _load_int8s nam arr adr = char_of_int(__load_int8 arr.(adr))\n");
  output_string fout ("let _load_int8u nam arr adr = Int32.of_int(__load_int8 arr.(adr))\n");
  output_string fout "\n";
  output_string fout ("let __store_float64 nam arr adr f =\n  let f' = Double (Int64.bits_of_float f) in arr.(adr) <- f'\n");
  output_string fout ("let __store_int64 nam arr adr n = arr.(adr) <- Long n\n");
  output_string fout ("let __store_any32 nam arr adr n = arr.(adr) <- Int n\n");
  output_string fout ("let __store_int32 nam arr adr n = arr.(adr) <- Int n\n");
  output_string fout ("let __store_int8u nam arr adr n = \n  let n' = Char (Int32.to_int n) in arr.(adr) <- n'\n");
  output_string fout "let __adr n = Int32.to_int n\n";
  output_string fout "\n";
  let p = {out=Buffer.create 4096;
           membuf=Buffer.create 4096;
           indent="  ";
           blocklbl=ref 0;
           stem="";
           nest=[];
           hashdata=hashdata;
	   prec'=0;
	   prec1=0;
	   prec2=0;
	   fmt=FmtNone;
           taskcnt = ref 0;
           top=false;
	   initoff=ref 0;
	   initfunc="";
           sig_res=None;
           boolcontext=false;
           exnbuf=Buffer.create 4096;
           fixed=false;
           topfunc=topfunc;
           hardware=false;
           pure=false;
	   assertions=[];
           chk=fmt;
           } in
  if not (Hashtbl.mem hashdata.intern topfunc) then
  failwith ("top function "^topfunc^" not found or invalid");
  let topfn = Hashtbl.find hashdata.intern topfunc in
  Hashtbl.add hashdata.extratasks topfunc topfn;
  Hashtbl.add hashdata.used topfunc ();
  while Hashtbl.length hashdata.extratasks > 0 do
      let (extralst:(string * intfn) list ref) = ref [] in
      Hashtbl.iter (fun id x -> print_endline ("Extra: "^id); extralst := (id,x) :: !extralst) hashdata.extratasks;
      Hashtbl.clear hashdata.extratasks;
      List.iter (fun (id,(x:intfn)) ->
        let (fn_callconv, fn_params, fn_vars, fn_body, fn_return) = x in
        print_endline ("List.iter "^id^" extralst");
      fprintf p.chk "%s@ "
		(name_cdecl (name_function_parameters id
						      fn_params fn_callconv)
			    fn_return);
      fprintf p.chk "@[<v 2>{@ ";
      List.iter
	(fun (id, ty) ->
	  fprintf p.chk "%s;@ " (name_cdecl id ty))
	fn_vars;
      print_cstmt p.chk fn_body;
      fprintf p.chk "@;<0 -2>}@]@ @ ";

        Hashtbl.replace hashdata.buffers id (0l,Buffer.create 4096);
        print_func {p with stem=id; out=snd(Hashtbl.find hashdata.buffers id)} id x) !extralst;
    done;
  Buffer.output_buffer fout p.exnbuf;
  Hashtbl.iter (fun id (_,_,gv) -> if Hashtbl.mem hashdata.used id then (
    let buf = Buffer.create 4096 in
    print_stmt {p with stem=id; out=buf} p.out gv;
    Buffer.output_buffer fout buf;
    )) hashdata.gvar;
  let olst = ref [] in
  Hashtbl.iter (fun id (gv,buf) -> olst := (id,gv,buf) :: !olst) hashdata.buffers;
  let olst = (List.sort Pervasives.compare !olst) in
  let rec dump id x = if Hashtbl.mem hashdata.used id then
        begin
	let deplst = Hashtbl.find_all hashdata.depend id in
	List.iter (fun id' ->
		       print_endline ("Find: "^id');
		       if id <> id' && Hashtbl.mem hashdata.buffers id' then
                           begin
		           print_endline ("Dump: "^id');
                           dump id' (snd(Hashtbl.find hashdata.buffers id'))
                           end) deplst;
        Buffer.output_buffer fout x;
	Hashtbl.remove hashdata.used id;
        end in
  List.iter (fun (id,n,x) -> dump id x) olst;
close_out fout

let dumpcombined hashdata topfunc =
  let outfile = "combined_"^topfunc^".ml" in
  try 
      Printexc.print (dumpcombined_exn hashdata outfile) topfunc;
  0
  with _ ->
  print_endline ("deleting: "^outfile);
  Sys.remove outfile;
  1

let gettree ctypes cvars cfun cext fmt sourcename =
    let ifile = Filename.temp_file "compcert" ".i" in
    Clflags.prepro_options := [];
    Clflags.prepro_options := "../simpleDMC_restructure/src" :: "-I" :: !Clflags.prepro_options;
    Clightgen.preprocess sourcename ifile;
    let prog = Clightgen.parse_c_file sourcename ifile in
    let oc = open_out (sourcename^".prog.csyntax") in
    PrintCsyntax.print_program (Format.formatter_of_out_channel oc) prog;
    close_out oc;
    trans_program ctypes cvars cfun cext prog fmt

let ctypes = Hashtbl.create 256
let cvars = Hashtbl.create 256
let cfun = Hashtbl.create 256
let cext = Hashtbl.create 256

let typlst = ref []
let varlst = ref []
let funlst = ref []
let extlst = ref []

let parse_files files outfile main =
    let oc = open_out (main^".chk.csyntax") in
    let fmt = Format.formatter_of_out_channel oc in    
    List.iter (gettree ctypes cvars cfun cext fmt) files;
    Hashtbl.iter (fun key itm -> typlst := (key,itm) :: !typlst) ctypes;
    Hashtbl.iter (fun key itm -> varlst := (key,itm) :: !varlst) cvars;
    Hashtbl.iter (fun key itm -> funlst := (key,itm) :: !funlst) cfun;
    Hashtbl.iter (fun key itm -> extlst := (key,itm) :: !extlst) cext;
    let hashdata = {extern=Hashtbl.create 256;
             intern=cfun;
             gvar=cvars;
             modes=Hashtbl.create 256;
             extratasks=Hashtbl.create 256;
             buffers=Hashtbl.create 256;
             memories=Hashtbl.create 256;
             used=Hashtbl.create 256;
             depend=Hashtbl.create 256;
             geval=Hashtbl.create 256;
             subs=[];
             buflst=ref [];
             unopt=Hashtbl.create 256} in
    dumpcombined_exn hashdata outfile main fmt;
    close_out oc;
    hashdata
