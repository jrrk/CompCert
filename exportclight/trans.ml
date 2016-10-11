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

open Format
open Camlcoq
open Datatypes
open Values
open AST
open PrintAST
open Ctypes
open Cop
open Clight
open Globalenvs
open Printf

let temp_name (id: AST.ident) = "_" ^ Z.to_string (Z.Zpos id)

let extern_atom a =
  try
    Hashtbl.find string_of_atom a
  with Not_found ->
    Printf.sprintf "_%d" (P.to_int a)

type trans = 
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
  | Assign of trans * trans
  | Set of string * trans
  | Call of trans * trans list
  | Extern of string * trans list * trans list
  | Builtin of string * trans list * trans list
  | Volatile_load of string * trans list * trans list
  | Volatile_store of string * trans list * trans list
  | Malloc of trans list * trans list
  | Free of trans list * trans list
  | Memcpy of int * int * trans list * trans list
  | Annot of string * trans list * trans list
  | Annot_val of string * trans list * trans list
  | Inline_asm of string * trans list * trans list
  | Debug of int * string * trans list * trans list
  | Ifthenelse of trans * trans list * trans list
  | While of int * trans list
  | For of trans list * trans list
  | Break
  | Continue
  | Switch of trans * trans list
  | Return of trans
  | Label of string * trans list
  | Goto of string
  | Case of string * trans list
  | Default of trans list
  | Tempvar of string * trans
  | Deref of trans * trans
  | Field of trans * string * trans
  | Const_int of int32 * trans
  | Const_float of float * trans
  | Const_long of int64 * trans
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
  | Alignas of int32 * trans
  | Attr of bool * trans
  | Array of trans * int32
  | Tbool
  | Tparams of string * trans * trans list
  | Tcallconv of bool * bool * bool
  | Tcc_default
  | Tdouble
  | Tfloat
  | Tfunc of trans list * trans * trans
  | The
  | This
  | Schar
  | Sshort
  | Sint
  | Slong
  | Tpointer
  | Tptr of trans
  | Tstruc of string
  | Uchar
  | Ushort
  | Uint
  | Ulong
  | Tuni of string
  | Void
  | Tvolatile of trans
  | Tvolatile_alignas of int32 * trans

let struct_or_union id = function Struct -> Tstruc id | Union -> Tuni id

let coqN n = N.to_int32 n

let coqint n = camlint_of_coqint n

let coqint64 n = camlint64_of_coqint n

let coqfloat n = Int64.float_of_bits (coqint64 (Floats.Float.to_bits n))

let coqsingle n = Int32.float_of_bits (coqint (Floats.Float32.to_bits n))

let rec attributes t = function
  | { attr_volatile = false; attr_alignas = None} ->
        rtyp t
  | { attr_volatile = true; attr_alignas = None} ->
        Tvolatile(rtyp t)
  | { attr_volatile = false; attr_alignas = Some n} ->
        Alignas(coqN n, rtyp t)
  | { attr_volatile = true; attr_alignas = Some n} ->
        Tvolatile_alignas(coqN n, rtyp t)

and typ t = attributes t (attr_of_type t)

and rtyp = function
  | Tvoid -> Void
  | Tint(sz, sg, _) ->
      (
        match sz, sg with
        | I8, Signed -> Schar
        | I8, Unsigned -> Uchar
        | I16, Signed -> Sshort
        | I16, Unsigned -> Ushort
        | I32, Signed -> Sint
        | I32, Unsigned -> Uint
        | IBool, _ -> Tbool)
  | Tlong(sg, _) ->
      (
        match sg with
        | Signed -> Slong
        | Unsigned -> Ulong)
  | Tfloat(sz, _) ->
      (
        match sz with
        | F32 -> Tfloat
        | F64 -> Tdouble)
  | Tpointer(t, _) ->
      Tptr (typ t)
  | Tarray(t, sz, _) ->
      Array(typ t, Z.to_int32 sz)
  | Tfunction(targs, tres, cc) ->
      Tfunc(typlist targs, typ tres, callconv cc)
  | Tstruct(id, _) ->
      Tstruc(extern_atom id)
  | Tunion(id, _) ->
      Tuni(extern_atom id)

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

let rec texpr = function
  | Evar(id, t) -> Var(extern_atom id, typ t)
  | Etempvar(id, t) -> Tempvar(extern_atom id, typ t)
  | Ederef(a1, t) -> Deref(texpr a1, typ t)
  | Efield(a1, f, t) -> Field(texpr a1, extern_atom f, typ t)
  | Econst_int(n, t) -> Const_int(coqint n, typ t)
  | Econst_float(n, t) -> Const_float(coqfloat n, typ t)
  | Econst_long(n, t) -> Const_long(coqint64 n, typ t)
  | Econst_single(n, t) -> Const_single(coqsingle n, typ t)
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

let builtin tyargs el = function
  | AST.EF_external(name, sg) -> Extern (camlstring_of_coqstring name, typlist tyargs, List.map texpr el)
  | EF_builtin(name, sg) -> Builtin (camlstring_of_coqstring name, typlist tyargs, List.map texpr el)
  | EF_vload chunk -> Volatile_load (name_of_chunk chunk, typlist tyargs, List.map texpr el)
  | EF_vstore chunk -> Volatile_store (name_of_chunk chunk, typlist tyargs, List.map texpr el)
  | EF_malloc -> Malloc(typlist tyargs, List.map texpr el)
  | EF_free -> Free(typlist tyargs, List.map texpr el)
  | EF_memcpy(sz, al) -> Memcpy(Z.to_int sz, Z.to_int al,typlist tyargs, List.map texpr el)
  | EF_annot(text, targs) -> Annot (camlstring_of_coqstring text, typlist tyargs, List.map texpr el)
  | EF_annot_val(text, targ) -> Annot_val (camlstring_of_coqstring text, typlist tyargs, List.map texpr el)
  | EF_inline_asm(text, sg, clob) -> Inline_asm (camlstring_of_coqstring text, typlist tyargs, List.map texpr el)
  | EF_debug(kind, text, targs) -> Debug(P.to_int kind, extern_atom text, typlist tyargs, List.map texpr el)

let rec tstmt = function
  | Sskip -> []
  | Sassign(e1, e2) -> [Assign(texpr e1, texpr e2)]
  | Sset(id, e2) -> [Set (temp_name id, texpr e2)]
  | Sbuiltin(None, ef, tyargs, el) -> [builtin tyargs el ef]
  | Sbuiltin(Some id, ef, tyargs, el) -> [Set(extern_atom id, builtin tyargs el ef)]
  | Scall(None, e1, el) -> [Call(texpr e1, List.map texpr el)]
  | Scall(Some id, e1, el) -> [Set(temp_name id, Call(texpr e1, List.map texpr el))]
  | Ssequence(Sskip, s2) -> tstmt s2
  | Ssequence(s1, Sskip) -> tstmt s1
  | Ssequence(s1, s2) -> tstmt s1 @ tstmt s2
  | Sifthenelse(e, s1, Sskip) -> [Ifthenelse(texpr e, tstmt s1, [])]
  | Sifthenelse(e, Sskip, s2) -> [Ifthenelse(texpr e, [], tstmt s2)]
  | Sifthenelse(e, s1, s2) -> [Ifthenelse(texpr e, tstmt s1, tstmt s2)]
  | Sloop(s1, Sskip) -> [While (1, tstmt s1)]
  | Sloop(s1, s2) -> [For(tstmt s2, tstmt s1)]
  | Sbreak -> [Break]
  | Scontinue -> [Continue]
  | Sswitch(e, cases) -> [Switch(texpr e, tcases cases)]
  | Sreturn None -> [Return Void]
  | Sreturn (Some e) -> [Return(texpr e)]
  | Slabel(lbl, s1) -> [Label(extern_atom lbl, tstmt s1)]
  | Sgoto lbl -> [Goto(extern_atom lbl)]

and tcases = function
  | LSnil -> []
  | LScons(None, s, rem) -> Default(tstmt s) :: tcases rem
  | LScons(Some lbl, s, rem) -> Case(Z.to_string lbl, tstmt s) :: tcases rem

let faillst = ref []
let discreplst = ref []
let errlst = ref []

let rec typcmp ctypes (key1, attr1, lst1) (key2, attr2, lst2) =
  let match1 = function
    | (Tstruc exp1, Tstruc exp2) -> exp1=exp2 || typcmp ctypes (Hashtbl.find ctypes exp1) (Hashtbl.find ctypes exp2)
    | (Tuni exp1, Tuni exp2) -> exp1=exp2 || typcmp ctypes (Hashtbl.find ctypes exp1) (Hashtbl.find ctypes exp2)
    | (_,_) -> false in
  match1 (key1, key2)

let trans_program ctypes cvars cfun cext prog =
  List.iter (function
    | Composite(id, su, m, a) -> let key = extern_atom id in
      let lst = List.map (fun (fid, fty) -> (extern_atom fid,typ fty)) m in
      let contents = (struct_or_union key su, attributes Tvoid a, lst) in
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
        let contents = (builtin args [] ef, typ res, callconv cconv) in
        if (Hashtbl.mem cext key) then assert(Hashtbl.find cext key = contents)
        else Hashtbl.add cext key contents
    | Gfun (Internal f) ->
          assert(Hashtbl.mem ctypes key == false);
          Hashtbl.add cfun key (
	  callconv f.fn_callconv, 
	  List.map (fun (id,ty) -> (extern_atom id, typ ty)) f.fn_params,
          List.map (fun (id, ty) -> (extern_atom id, typ ty)) f.fn_vars,
          List.map (fun (id, ty) -> (temp_name id, typ ty)) f.fn_temps,
          tstmt f.fn_body)
    | Gvar v -> let tinit = List.map (function
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

type intfn = trans * (string * trans) list * (string * trans) list *
    (string * trans) list * trans list

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
  | Tbool -> "bool"
  | Schar -> "signed char"
  | Uchar -> "unsigned char"
  | Sshort -> "signed short"
  | Ushort -> "unsigned short"
  | Sint -> "signed int"
  | Uint -> "unsigned int"
  | Slong -> "signed long"
  | Ulong -> "unsigned long"
  | Tfloat -> "float"
  | Tdouble -> "float"
  | Tptr t -> name_of_type t^" *"
  | Tstruc s -> "struct_"^s
  | Tuni s -> "uni_"^s
  | Void -> "unit"
  | Array (typ, len) -> name_of_type typ^" array"
  | oth -> othlst := oth :: !othlst; myfail "name_of_type" oth

let rec init_of_type = function
  | Tbool -> "false"
  | Schar -> "'0'"
  | Uchar -> "'0'"
  | Sshort -> "0"
  | Ushort -> "0"
  | Sint -> "0"
  | Uint -> "0"
  | Slong -> "0l"
  | Ulong -> "0l"
  | Tfloat -> "0f"
  | Tdouble -> "0f"
  | Tptr (Tptr Schar) -> "\"\""
  | Tptr (Tstruc s) -> "ref ()"
  | Tptr (Tuni s) -> "ref ()"
  | Tptr (Tdouble) -> "ref 0.0"
  | Tptr (Schar) -> "ref ' '"
  | Tptr (Sshort) -> "ref 0"
  | Tptr (Void) -> "ref ()"
  | Tptr oth -> "ref ("^init_of_type oth^")"
  | Tstruc s -> "struc_"^s
  | Tuni u -> "uni_"^u
  | Array (typ, len) -> "Array.make "^Int32.to_string len^ (init_of_type typ)
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

(* Statements *)
let rec print_stmt' p = function
  | Debug(n,str,args,sg) -> bprintf p.out "(*skip*)";
  | Set(lhs, rhs) -> bprintf p.out "%s := %a;" lhs (print_expr p) rhs; 
  | Tmul(lhs, rhs, ty) -> bprintf p.out "%a * %a;" (print_expr p) lhs (print_expr p) rhs; 
  | Field (Var (lhs, Tstruc _), rhs, ty) -> bprintf p.out "%s.%s" lhs rhs;
  | Sizeof (ty, Uint) -> bprintf p.out "sizeof(%s)" (name_of_type ty);
(*
  | Call([], Qaddrsymbol("__assert_fail", Qintconst 0l), el, sg) ->
      bprintf p.out "Printf.printf \"Assertion failed: %%s location %%s:%%ld, function %%s\", ";
      bprintf p.out "%a; Pervasives.exit 1;\n%s" (print_expr_list {p with fmt=FmtPrintf}) (true, el) p.indent;
     
  | Call(retval, Qaddrsymbol("abort", Qintconst 0l), el, sg) ->
      bprintf p.out "Pervasives.exit 2;\n%s" p.indent;
     
  | Call(retval, Qaddrsymbol("fflush", Qintconst 0l), Qload(Mint32, Qaddrsymbol(stream, Qintconst 0l))::args, sg) ->
      bprintf p.out "flush %s " (stream' stream);
      bprintf p.out "%a;" (print_expr_list p) (false, args @ retval);
     
  | Call(retval, Qaddrsymbol("exit", Qintconst 0l), el, sg) ->
      bprintf p.out "Pervasives.exit 0;\n%s" p.indent;
     
  | Call(retval, Qaddrsymbol("printf", Qintconst 0l), Qinitstr inithd::inittl, sg) ->
      bprintf p.out "\n%sPrintf.printf %s" p.indent (format_cnv inithd);
      List.iter (fun itm -> bprintf p.out " (%a)" (print_expr {p with fmt=FmtPrintf}) itm) inittl;
      bprintf p.out ";\n%s" p.indent;
     
  | Call(retval, Qaddrsymbol("fprintf", Qintconst 0l), Qload(Mint32, Qaddrsymbol(stream, Qintconst 0l))::Qinitstr inithd::inittl, sg) ->
      bprintf p.out "\n%sPrintf.fprintf %s %s" p.indent (stream' stream) (format_cnv inithd);
      List.iter (fun itm -> bprintf p.out " (%a)" (print_expr {p with fmt=FmtPrintf}) itm) inittl;
      bprintf p.out ";\n%s" p.indent;
     
  | Call _ as err -> calllst := (p, err) :: !calllst; myfail "Qcall" err
  | Qtailcall(e1, el, sg) ->
      bprintf p.out "tailcall %a,(%a) : %a"
                (print_expr p) e1
                (print_expr_list p) (true, el)
                print_sig sg;
  | Qbuiltin(id, ext, el, ef) ->
      (match id with Some str -> bprintf p.out "%s = " (str) | None -> ());
      bprintf p.out "builtin_%s(%a);"
                (name_of_external ext)
                (print_expr_list p) (true, el);
  | Qifthenelse(e, s1, []) ->
      bprintf p.out "\n%sif %a then begin\n%s" p.indent (print_expr {p with boolcontext=true}) e p.indent;
      print_stmt' {p with indent="  "^p.indent} s1;
      bprintf p.out "\n%send;\n%s"
          p.indent
          p.indent; 
     
  | Qifthenelse(e, s1, s2) ->
      bprintf p.out "\n%sif %a then\n%s begin\n%s " p.indent (print_expr {p with boolcontext=true}) e p.indent p.indent;
      print_stmt' {p with indent="  "^p.indent} s1;
      bprintf p.out "\n%s  end\n%selse\n%s  begin\n%s  "
          p.indent
          p.indent
          p.indent
          p.indent;
      print_stmt' {p with indent="  "^p.indent} s2;
      bprintf p.out "\n%s  end;\n%s" p.indent p.indent;
     
  | Qexit n ->
      bprintf p.out "raise Block_%s;" (List.nth p.nest n);
     
  | Qcase(n, x) ->
      bprintf p.out "| %Ldl -> raise Block_%s;\n%s" n (List.nth p.nest x) p.indent;
     
  | Qswitch(long, e, cases, dfl) ->
      bprintf p.out "begin match %a with\n%s" (print_expr p) e  p.indent;
      print_stmt' p cases;
      bprintf p.out "| _ -> raise Block_%s;\n%send;\n%s" (List.nth p.nest dfl) p.indent p.indent;
     
  | Qreturn None ->
      bprintf p.out "raise Block_%s;" p.stem;
     
  | Qreturn (Some e) ->
      bprintf p.out "r_%s._%s_res := %a;\n" p.stem p.stem (print_expr p) e;
      bprintf p.out "%sraise Block_%s;" p.indent p.stem;
     
  | Qlabel(lbl, s1) ->
      bprintf p.out "%s: " (lbl); print_stmt p s1;  (* wrong for Cminorgen output *)
  | Qgoto lbl ->
      bprintf p.out "goto %s;" (lbl);               (* wrong for Cminorgen output *)
  | Qvar(id,typ) ->
      if p.fmt = FmtLhs then
          bprintf p.out " r_%s._%s_%s" p.stem p.stem id
      else
          bprintf p.out " !(r_%s._%s_%s)" p.stem p.stem id;
      Hashtbl.replace p.hashdata.used id ();
     
  | Qintconst n ->
      bprintf p.out "%ldl" n; 
     
  | Qfloatconst f ->
      let f' = Int64.bits_of_float f in bprintf p.out "Int64.float_of_bits(0x%.16LXL)" f';
     
  | Qsingleconst f ->
      bprintf p.out "32'h%.8lX" (Int32.bits_of_float f); 
     
  | Qlongconst n -> bprintf p.out "0x%.16LxL" n;
  | Qaddrsymbol(id, a1) ->
      bprintf p.out "%s + " (id);
      bprintf p.out "%a" (expr p) (p.prec', a1);
      Hashtbl.replace p.hashdata.used id ();
  | Qunop(op, a1) ->
      bprintf p.out "%s(%a)" (name_of_unop op) (expr p) (p.prec', a1);
     
  | Qbinop((Ocmp _|Ocmpl _|Ocmpf _|Ocmpfs _) as op, a1, a2) when p.boolcontext -> bprintf p.out "%a %s %a" (expr p) (p.prec1, a1) (name_of_binop op) (expr p) (p.prec2, a2); 
     
  | Qbinop((Ocmp _|Ocmpl _|Ocmpf _|Ocmpfs _) as op, a1, a2) -> bprintf p.out "(if %a %s %a then 1l else 0l)" (expr p) (p.prec1, a1) (name_of_binop op) (expr p) (p.prec2, a2);
     
  | Qbinop(op, a1, a2) ->
      bprintf p.out "%a %s %a" (expr p) (p.prec1, a1) (name_of_binop op) (expr p) (p.prec2, a2);
     
  | Qload(chunk, Qaddrsymbol(str, Qintconst 0l)) when Opt_body.readonlyv p.hashdata.gvar str ->
      Hashtbl.replace p.hashdata.used str ();
      (match Hashtbl.find p.hashdata.gvar str with
        | Qglobvar (str', true, _, Qinit [Qint32 ro]) when str=str' ->
            bprintf p.out "(*%s*) %ldl" (name_of_chunk chunk) ro
        | Qglobvar (str', true, _, Qinit [Qfloat64 ro]) when str=str' ->
            bprintf p.out "(*%s*) (Int64.float_of_bits 0x%.16LXL)" (name_of_chunk chunk) (Int64.bits_of_float ro)
        | oth -> rolst := oth :: !rolst; myfail "failed to optimise read-only global" oth);
     
  | Qload(chunk, (Qaddrsymbol(str, expr1))) ->
      let modes = Hashtbl.find_all p.hashdata.modes str in
      if Library.comment_verbose then begin
        bprintf p.out " (*";
        List.iter (fun itm -> bprintf p.out " %s" (name_of_chunk itm)) (List.sort compare modes);
        bprintf p.out " *)";
        end;
      let siz = (size_of_chunk chunk) in
      let nam = name_of_chunk chunk in
      let off = Library.simplify_expr p.hashdata.modes (Qadd [Qintconst (Int32.of_int 0); expr1]) in
      bprintf p.out "(_load_%s \"_%s\" _%s (__adr(%a)))" nam (str^"(*"^nam^"*)") str (print_expr p) off;
      Hashtbl.replace p.hashdata.used str ();
     
  | Qload _ as err -> loadlst := err :: !loadlst; myfail "Qload" err
  | Qinitstr str -> bprintf p.out "%s" str;
  | Qadd [] -> bprintf p.out "0";
  | Qadd (addhd::addtl) ->
     bprintf p.out "%a" (expr p) (p.prec1, addhd);
     List.iter (fun itm -> bprintf p.out " +@ %a" (expr p) (p.prec2, itm)) addtl;
  | Qinit lst -> print_stmt p lst;
  | Qint8 n ->
      bprintf p.out "| %4d -> Char 0x%.2lX\n" !(p.initoff) (Int32.logand n 255l);
      incr p.initoff;
     
  | Qint16 n -> 
      bprintf p.out "| %4d -> Short 0x%.4lX\n" !(p.initoff) (Int32.logand n 65535l);
      p.initoff := 2 + !(p.initoff);
     
  | Qint32 n ->
      bprintf p.out "| %4d -> Int 0x%.8lXl\n" !(p.initoff) n;
      p.initoff := 4 + !(p.initoff);
     
  | Qint64 n ->
      bprintf p.out "| %4d -> Long 0x%.16LXL\n" !(p.initoff) n;
      p.initoff := 8 + !(p.initoff);
     
  | Qfloat32 f ->
      let n = Int32.bits_of_float f in
      bprintf p.out "| %4d -> Float 0x%.4lX\n" !(p.initoff) n;
      p.initoff := 4 + !(p.initoff);
     
  | Qfloat64 f ->
      let n = Int64.bits_of_float f in
      bprintf p.out "| %4d -> Double 0x%.16LXL\n" !(p.initoff) n;
      p.initoff := 8 + !(p.initoff);
     
  | Qspace n ->
      p.initoff := (Int32.to_int n) + !(p.initoff);
     
  | Qaddrof (off, id) ->
      bprintf p.out "| %4d -> Addrof 0x0\n" !(p.initoff);
      p.initoff := 4 + !(p.initoff);
     
  | Qglobvar (id, gvar_readonly, gvar_volatile, init) ->
      let space = init_length id init in
      let typ = match Hashtbl.find_all p.hashdata.modes id with
        | Mfloat64 :: [] -> Tlong
        | Mint32 :: [] -> Tint
        | Mint64 :: [] -> Tlong
        | Mint64 :: Mfloat64 :: [] -> Tlong
        | oth -> typlst := oth :: !typlst; Tunknown in
        (match init with
          | Qinit [Qspace n] ->
             bprintf p.out "let init_%s sel = Int 0l\n" id;
          | oth ->
             bprintf p.out "let init_%s = function\n" id;
             print_stmt' {p with initoff=ref 0} [init];
             bprintf p.out "| _ -> Void (* end function init_%s *)\n" id;
            );
	bprintf p.out "let _%s = Array.init %ld init_%s " id space id;
        if (gvar_readonly) then
          bprintf p.out " (* readonly *)";
        if (gvar_volatile) then
          bprintf p.out " (* volatile *)";
        bprintf p.out "\n";
       
  | Qinput _ as err -> myfail "Qinput" err
  | Qoutput _ as err -> myfail "Qoutput" err
*)
  | Call(Var(id, sg), modargs) as call ->
      print_endline ("Call("^p.stem^"): "^id);
      bprintf p.out "task_%s" id;
      List.iter (fun itm -> bprintf p.out " (%a)" (print_expr p) itm) modargs;
      if modargs <> [] then bprintf p.out ";\n%s" p.indent else bprintf p.out " ();\n%s" p.indent;
      Hashtbl.replace p.hashdata.used id ();
      if p.stem <> id then Hashtbl.add p.hashdata.depend p.stem id;
      if p.stem <> id && Hashtbl.mem p.hashdata.intern id then
          begin
          print_endline ("Local call: "^id);
          Hashtbl.add p.hashdata.extratasks id (Hashtbl.find p.hashdata.intern id);
          end;
     
  | Tempvar (arg, ty) -> bprintf p.out "%s" arg;
     
  | Taddrof (vexp, typ) -> bprintf p.out "ref %a" (print_expr p) vexp;
     
  | Const_int (n, Sint) -> bprintf p.out "%ld" n;
     
  | Teq (lft, rght, Sint) -> bprintf p.out "%a = %a" (print_expr p) lft (print_expr p) rght;
  | Tne (lft, rght, Sint) -> bprintf p.out "%a <> %a" (print_expr p) lft (print_expr p) rght;
  | Tgt (lft, rght, Sint) -> bprintf p.out "%a > %a" (print_expr p) lft (print_expr p) rght;
  | Tge (lft, rght, Sint) -> bprintf p.out "%a >= %a" (print_expr p) lft (print_expr p) rght;
  | Tlt (lft, rght, Sint) -> bprintf p.out "%a < %a" (print_expr p) lft (print_expr p) rght;
  | Tle (lft, rght, Sint) -> bprintf p.out "%a <= %a" (print_expr p) lft (print_expr p) rght;
     
  | Tadd (lft, rght, typ) -> bprintf p.out "%a + %a" (print_expr p) lft (print_expr p) rght;
  | Tsub (lft, rght, typ) -> bprintf p.out "%a - %a" (print_expr p) lft (print_expr p) rght;
  | Tmul (lft, rght, typ) -> bprintf p.out "%a * %a" (print_expr p) lft (print_expr p) rght;
  | Tdiv (lft, rght, typ) -> bprintf p.out "%a / %a" (print_expr p) lft (print_expr p) rght;
  | Tshr (lft, rght, typ) -> bprintf p.out "%a lsr %a" (print_expr p) lft (print_expr p) rght;
  | Tnotbool (lft, typ) -> bprintf p.out "!%a" (print_expr p) lft
  | Tneg (lft, typ) -> bprintf p.out "-%a" (print_expr p) lft
  | Taddlst (typ, lst) -> let delim = ref ' ' in 
      List.iter (fun itm -> bprintf p.out "%c%a" !delim (print_expr p) itm; delim := '+') lst
  | Var (nam, Array (Schar, len)) when String.length nam > 12 && String.sub nam 0 12 = "__stringlit_" ->
      if Hashtbl.mem p.hashdata.gvar nam then
      (let (readonly, init, info) = Hashtbl.find p.hashdata.gvar nam in
      bprintf p.out "\"";
      List.iter (function Char itm -> bprintf p.out "%c" (char_of_int itm) | _ -> failwith "init") init;
      bprintf p.out "\"")
      else bprintf p.out "\"%s\"" (String.escaped nam);
  | Var (nam, typ) -> bprintf p.out "%s" nam;
  | Const_float(arg, Tdouble) -> bprintf p.out "%f" arg
  | Void -> bprintf p.out "()"
  | Ifthenelse (condition,
    thenlst,
    elselst) ->
      bprintf p.out "if %a then " (print_expr p) condition;
      bprintf p.out " (%a)" (print_stmt_list p) thenlst;
      bprintf p.out " else ";
      bprintf p.out " (%a)" (print_stmt_list p) elselst
  | Assign (dest, expr) -> bprintf p.out "%a = %a" (print_expr p) dest (print_expr p) expr
  | Cast (temp, typ) -> bprintf p.out "Cast(%a, %s)" (print_expr p) temp (name_of_type typ)
  | For ([Ifthenelse (exp, [], [Break])], looplst) ->
      bprintf p.out "while %a do %a; done" (print_expr p) exp (print_stmt_list p) looplst
  | For ([Set (dst, expr)], looplst) ->
      bprintf p.out "For(Set(%s, %a); %a)" dst (print_expr p) expr (print_stmt_list p) looplst
  | For ([Break], looplst) ->
      bprintf p.out "while true do %a; done" (print_stmt_list p) looplst
  | While (exp, looplst) ->
      bprintf p.out "while %d do %a done" exp (print_stmt_list p) looplst
  | Return expr -> bprintf p.out "rslt_%s := %a; raise Block_%s;" p.stem (print_expr p) expr p.stem
  | Field (Deref (Tempvar (ptr, Tptr (Tstruc info1)), Tstruc info2), fld, typ) when info1=info2 ->
      bprintf p.out "%s->%s" ptr fld
  | Field (exp, nam, typ) -> bprintf p.out "%a->%s" (print_expr p) exp nam
  | Deref (Tadd (Tempvar (ptr, Tptr typ), Tempvar (tmp, tmptyp), Tptr typ'), typ'') when typ=typ' && typ'=typ'' ->
      bprintf p.out "!%s" ptr
  | Deref (exp, typ) ->
      bprintf p.out "!%a" (print_expr p) exp
  | Switch (exp, caselst) -> bprintf p.out "match %a with %a" (print_expr p) exp (print_stmt_list p) caselst
  | Case (itm, stmtlst) -> bprintf p.out "| %s -> %a" itm (print_stmt_list p) stmtlst
  | Default stmtlst -> bprintf p.out "| _ -> %a" (print_stmt_list p) stmtlst
  | Break -> bprintf p.out "raise Break_%s" p.stem
  | Continue -> bprintf p.out "raise Continue_%s" p.stem
  | Goto dest -> bprintf p.out "raise Goto_%s_%s" p.stem dest
  | Label (dest,lst) -> bprintf p.out "with Goto_%s_%s -> %a" p.stem dest (print_stmt_list p) lst
  | err -> errlst := err :: !errlst; myfail "Other" err

and expr p out (prec, e) =
  let (prec', assoc) = precedence e in
  let (prec1, prec2) =
    if assoc = LtoR
    then (prec', prec' + 1)
    else (prec' + 1, prec') in
  if prec' < prec
  then bprintf out "("
  else bprintf out "";
  print_stmt {p with prec'=prec'; prec1=prec1; prec2=prec2} [e];
  if prec' < prec then bprintf out ")"

and print_expr p out e = expr p out (0, e)

and print_expr_list p out (first, rl) =
  match rl with
  | [] -> ()
  | r :: rl ->
      if not first then bprintf out ", ";
      expr p out (2, r);
      print_expr_list p out (false, rl)

and print_stmt p x =
  List.iter (print_stmt' p) x

and print_stmt_list p out = function
  | [] -> ()
  | r :: rl ->
      bprintf out ";\n\t";
      print_stmt' p r;
      print_stmt_list p out rl

(* Functions *)

and print_func p fn_id (callconv, fn_params, fn_vars, fn_temps, fn_body) =
(*
 (fn_id,
	fn_params,
	fn_sig,
	fn_stackspace,
	fn_vars,
	fn_body,
        fn_spec) = *)
  assert(p.stem=fn_id);
  bprintf p.out "type vars_%s = {\n" p.stem;
  List.iter  (fun (k,t) -> bprintf p.out "_%s_%s: %s ref;\n" p.stem k (name_of_type t)) (fn_params @ fn_vars);
(*
  (match fn_sig.sig_res with
    | Some t -> bprintf p.out "_%s_res: %s ref;" p.stem (name_of_type t)
    | None -> bprintf p.out "_%s_res: unit ref;" p.stem);
*)
  bprintf p.out "}\n\n";
  bprintf p.out "type dbg_%s = {\n" p.stem;
  List.iter  (fun (k,t) -> bprintf p.out "dbg_%s_%s: %s;\n" p.stem k (name_of_type t)) (fn_params @ fn_vars);
(*
  (match fn_sig.sig_res with
    | Some t -> bprintf p.out "dbg_%s_res: %s;" p.stem (name_of_type t)
    | None -> bprintf p.out "dbg_%s_res: unit;" p.stem);
*)
  bprintf p.out "}\n\n";
  bprintf p.out "let copy_%s src = {\n" p.stem;
  List.iter  (fun (k,t) -> bprintf p.out "dbg_%s_%s = !(src._%s_%s);\n" p.stem k p.stem k) (fn_params @ fn_vars);
  bprintf p.out "dbg_%s_res = !(src._%s_res);\n" p.stem p.stem;
  bprintf p.out "}\n\n";
  bprintf p.out "let (dbg_%s_lst:(string*dbg_%s*algebraic array) list ref) = ref []\n\n" p.stem p.stem;
  bprintf p.out "let r_%s = {\n" p.stem;
  List.iter  (fun (k,t) -> bprintf p.out "_%s_%s = ref %s;\n" p.stem k (init_of_type t)) (fn_params @ fn_vars);
(*
  (match fn_sig.sig_res with
    | Some t -> bprintf p.out "_%s_res = ref %s;\n" p.stem (init_of_type t)
    | None -> bprintf p.out "_%s_res = ref ();\n" p.stem);
*)
  bprintf p.out "}\n\n";
  bprintf p.out "let task_%s" p.stem;
  if fn_params <> [] then
      List.iter (fun (k,ty) -> bprintf p.out " (_%s:%s)" k (name_of_type ty)) fn_params
  else
      bprintf p.out " ()";
(*
  (match fn_sig.sig_res with
    | Some t -> bprintf p.out ": %s =\n" (name_of_type t)
    | None -> bprintf p.out ": unit =\n");
*)
  List.iter  (fun (k,t) -> bprintf p.out "r_%s._%s_%s := _%s;\n" p.stem p.stem k k) fn_params;
  bprintf p.out "begin\ndbg_%s_lst := [];\n\n" p.stem;
  bprintf p.out "%stry (* %s *)\n%s" p.indent p.stem p.indent;
  bprintf p.exnbuf "exception Block_%s\n" p.stem;
  print_stmt {p with indent="  "^p.indent (*; sig_res=fn_sig.sig_res *)} fn_body;
  bprintf p.out "\n%swith Block_%s -> ()\nend;\n" p.indent p.stem;
  bprintf p.out "!(r_%s._%s_res)\n (* task_%s *)\n\n" p.stem p.stem p.stem

let rec print_varlist p (vars, first) =
  match vars with
  | [] -> ()
  | v1 :: vl ->
      if not first then bprintf p.out ", ";
      bprintf p.out "%s" (v1);
      print_varlist p (vl, false)

let rec print_init_data_list p = function
  | [] -> ()
  | [item] -> print_stmt p [item]
  | item::rest ->
      (print_stmt p [item];
       bprintf p.out ",";
       print_init_data_list p rest)

let dumpcombined_exn hashdata outfile topfunc =
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
           } in
  if not (Hashtbl.mem hashdata.intern topfunc) then
  failwith ("top function "^topfunc^" not found or invalid");
  let topfn = Hashtbl.find hashdata.intern topfunc in
  let (callconv, fn_params, fn_vars, fn_temps, fn_body) = topfn in
  Hashtbl.add hashdata.extratasks topfunc topfn;
  Hashtbl.add hashdata.used topfunc ();
  while Hashtbl.length hashdata.extratasks > 0 do
      let (extralst:(string * intfn) list ref) = ref [] in
      Hashtbl.iter (fun id x -> print_endline ("Extra: "^id); extralst := (id,x) :: !extralst) hashdata.extratasks;
      Hashtbl.clear hashdata.extratasks;
      List.iter (fun (id,(x:intfn)) ->
        print_endline ("List.iter "^id^" extralst");
        Hashtbl.replace hashdata.buffers id (0l,Buffer.create 4096);
        print_func {p with stem=id; out=snd(Hashtbl.find hashdata.buffers id)} id x) !extralst;
    done;
  Buffer.output_buffer fout p.exnbuf;
  Hashtbl.iter (fun id (_,_,gv) -> if Hashtbl.mem hashdata.used id then (
    let buf = Buffer.create 4096 in
    print_stmt {p with stem=id; out=buf} [gv];
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

let clight csyntax =
    match SimplExpr.transl_program csyntax with
    | Errors.OK p ->
        begin match SimplLocals.transf_program p with
        | Errors.OK p' -> p'
        | Errors.Error msg ->
            Clightgen.print_error stderr msg;
            exit 2
        end
    | Errors.Error msg ->
        Clightgen.print_error stderr msg;
        exit 2

let gettree ctypes cvars cfun cext sourcename =
    let ifile = Filename.temp_file "compcert" ".i" in
    Clflags.prepro_options := [];
    Clflags.prepro_options := "../simpleDMC_restructure/src" :: "-I" :: !Clflags.prepro_options;
    Clightgen.preprocess sourcename ifile;
    trans_program ctypes cvars cfun cext (clight (Clightgen.parse_c_file sourcename ifile))

let ctypes = Hashtbl.create 256
let cvars = Hashtbl.create 256
let cfun = Hashtbl.create 256
let cext = Hashtbl.create 256

let typlst = ref []
let varlst = ref []
let funlst = ref []
let extlst = ref []

let parse_files files outfile main =
    List.iter (gettree ctypes cvars cfun cext) files;
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
    dumpcombined_exn hashdata outfile main;
    hashdata