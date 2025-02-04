(* Import *)

open Format
open X86_64
open Ast
open Compile_utils
open Compile_algo

(* Compile expr *)

let rec compile_expr (e : Ast.expr) : X86_64.text =
  match e.expr_desc with
  | Econstant cst -> nop
  | Eprint expr -> nop
  | _ -> failwith "Others expr todo"

(* Compile stmt *)

let rec compile_stmt : Ast.stmt -> X86_64.text = function
  | Sexpr expr -> compile_expr expr
  | Sblock stmts -> compile_stmts stmts
  | _ -> failwith "Others stmt todo"

and compile_stmts (stmts : Ast.stmt list) =
  List.fold_left (fun acc stmt -> acc ++ compile_stmt stmt) nop stmts

(* Compile decl *)

let compile_decl (cls : Ast.class_) : Ast.decl -> X86_64.text = function
  | Dconstructor (vars, stmt) -> failwith "Dconstructor todo"
  | Dmethod (meth, stmt) -> get_label_meth cls meth ++ compile_stmt stmt

let compile_decls (cls : Ast.class_) (decls : Ast.decl list) =
  List.fold_left (fun acc decl -> acc ++ compile_decl cls decl) nop decls

(* Compile class *)

let compile_class ((cls, decls) : Ast.tclass) : X86_64.text = compile_decls cls decls

let compile_classes (p : Ast.tfile) =
  List.fold_left (fun acc class_ -> acc ++ compile_class class_) nop p

(* Main *)

let file ?debug:(b = false) (p : Ast.tfile) : X86_64.program =
  debug := b;

  { text = globl "main" ++ label "main" ++ call label_main ++ ret ++ compile_classes p; data = nop }
