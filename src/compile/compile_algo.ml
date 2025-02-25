(* Import *)

open Compile_utils
open Ast
open X86_64

(* Data *)

let get_label_data, new_label_data =
  let cpt = ref ~-1 in

  let gld () = Format.sprintf ".D%d" !cpt in

  let nld () =
    incr cpt;
    Format.sprintf ".D%d" !cpt
  in

  (gld, nld)

(* And *)

let rewrite_and e1 e2 =
  let cond =
    make_expr (Ebinop (Beq, e1, make_expr (Econstant (Cint (Int32.of_int 0))) Tint)) Tboolean
  in
  let s1 = Sexpr (make_expr (Econstant (Cint (Int32.of_int 0))) Tint) in
  let s2 = Sexpr e2 in
  Sif (cond, s1, s2)

(* Or *)

let rewrite_or e1 e2 =
  let cond =
    make_expr (Ebinop (Beq, e1, make_expr (Econstant (Cint (Int32.of_int 1))) Tint)) Tboolean
  in
  let s1 = Sexpr (make_expr (Econstant (Cint (Int32.of_int 1))) Tint) in
  let s2 = Sexpr e2 in
  Sif (cond, s1, s2)

(* If *)

let compile_if :
     (Ast.expr -> X86_64.text)
  -> (Ast.stmt -> X86_64.text)
  -> Ast.expr
  -> Ast.stmt
  -> Ast.stmt
  -> X86_64.text =
  let cpt = ref ~-1 in
  fun compile_expr compile_stmt e s1 s2 ->
    incr cpt;
    let label_else = Format.sprintf "if_else_%d" !cpt in
    let label_done = Format.sprintf "if_done_%d" !cpt in

    compile_expr e ++ popq r10
    ++ cmpq (imm 0) !%r10
    ++ je label_else ++ compile_stmt s1 ++ jmp label_done ++ label label_else ++ compile_stmt s2
    ++ label label_done

(* For *)

let compile_for :
     (Ast.expr -> X86_64.text)
  -> (Ast.stmt -> X86_64.text)
  -> Ast.stmt
  -> Ast.expr
  -> Ast.stmt
  -> Ast.stmt
  -> X86_64.text =
  let cpt = ref ~-1 in
  fun compile_expr compile_stmt s1 e s2 s3 ->
    incr cpt;
    let label_do = Format.sprintf "for_do_%d" !cpt in
    let label_done = Format.sprintf "for_done_%d" !cpt in

    compile_stmt s1 ++ label label_do ++ compile_expr e ++ jne label_done ++ compile_stmt s2
    ++ compile_stmt s3 ++ jmp label_do ++ label label_done

(* Printf *)

let compile_printf () : text =
  label label_print_function ++ pushq !%rbp ++ movq !%rsp !%rbp
  ++ andq (imm ~-16) !%rsp
  ++ movq !%rdi !%rsi
  ++ movq (ilab label_print_data) !%rdi
  ++ xorq !%rax !%rax ++ call "printf" ++ movq !%rbp !%rsp ++ popq rbp ++ ret
