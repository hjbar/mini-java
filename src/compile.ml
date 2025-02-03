open Format
open X86_64
open Ast

let debug = ref false

let rec compile_expr (e : Ast.expr) : X86_64.text =
  match e.expr_desc with
  | Econstant cst -> nop
  | Eprint expr -> nop
  | _ -> failwith "Others expr todo"

let rec compile_stmt : Ast.stmt -> X86_64.text = function
  | Sexpr expr -> compile_expr expr
  | Sblock stmts -> List.fold_left (fun acc stmt -> acc ++ compile_stmt stmt) nop stmts
  | _ -> failwith "Others stmt todo"

let compile_decl : Ast.decl -> X86_64.text = function
  | Dconstructor (vars, stmt) -> failwith "Dconstructor todo"
  | Dmethod (meth_, stmt) -> compile_stmt stmt

let file ?debug:(b = false) (p : Ast.tfile) : X86_64.program =
  debug := b;

  { text =
      globl "main" ++ label "main" ++ call "C_Main_main" ++ ret
      ++ List.fold_left
           (fun acc (cls, decls) ->
             acc ++ List.fold_left (fun acc decl -> acc ++ compile_decl decl) nop decls )
           nop p
  ; data = nop
  }
