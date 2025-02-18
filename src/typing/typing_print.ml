(* Import *)

open Ast

(* Print classes *)

let print_class c = Format.printf "Class %s Extends %s@\n" c.class_name c.class_extends.class_name

let print_classes classes = Hashtbl.iter (fun _ c -> print_class c) classes

(* Print expr *)

let print_pexpr_desc (p : pexpr_desc) =
  Format.printf
  @@
  match p with
  | PEconstant c -> "PEconstant@\n"
  | PEbinop (b, e1, e2) -> "PEbinop@\n"
  | PEunop (u, e) -> "PEunop@\n"
  | PEthis -> "PEthis@\n"
  | PEnull -> "PEnull@\n"
  | PEident i -> "PEident@\n"
  | PEdot (e, i) -> "PEdot@\n"
  | PEassign_ident (i, e) -> "PEassign_ident@\n"
  | PEassign_dot (e, i, e2) -> "PEassign_dot@\n"
  | PEnew (i, l) -> "PEnew@\n"
  | PEcall (e, i, l) -> "PEcall@\n"
  | PEcast (t, e) -> "PEcast@\n"
  | PEinstanceof (e, t) -> "PEinstanceof@\n"

(* Print stmt *)

let print_stmt_desc (p : pstmt_desc) =
  Format.printf
  @@
  match p with
  | PSexpr e -> "PSexpr@\n"
  | PSvar (t, i, e) -> "PSvar@\n"
  | PSif (e, s1, s2) -> "PSif@\n"
  | PSreturn e -> "PSreturn@\n"
  | PSblock l -> "PSblock@\n"
  | PSfor (s1, e, s2, s3) -> "PSfor@\n"
