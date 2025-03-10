(* Import *)

open Ast
open X86_64
open Compile_utils

(* String *)

let compile_string : string -> data_queue -> X86_64.text =
  let cpt = ref ~-1 in
  fun (string : string) (queue : data_queue) ->
    incr cpt;
    let label = Format.sprintf ".D%d" !cpt in

    Queue.push (label, string) queue;
    pushq (ilab label)

(* And *)

let compile_and : (Ast.expr -> X86_64.text) -> Ast.expr -> Ast.expr -> X86_64.text =
  let cpt = ref ~-1 in
  fun compile_expr e1 e2 ->
    incr cpt;
    let label_done = Format.sprintf "and_done_%d" !cpt in

    compile_expr e1 ++ popq r12
    ++ cmpq (imm 0) !%r12
    ++ je label_done ++ compile_expr e2 ++ popq r12 ++ label label_done ++ pushq !%r12

(* Or *)

let compile_or : (Ast.expr -> X86_64.text) -> Ast.expr -> Ast.expr -> X86_64.text =
  let cpt = ref ~-1 in
  fun compile_expr e1 e2 ->
    incr cpt;
    let label_done = Format.sprintf "or_done_%d" !cpt in

    compile_expr e1 ++ popq r12
    ++ cmpq (imm 1) !%r12
    ++ je label_done ++ compile_expr e2 ++ popq r12 ++ label label_done ++ pushq !%r12

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

    compile_expr e ++ popq r12
    ++ cmpq (imm 0) !%r12
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

    compile_stmt s1 ++ label label_do ++ compile_expr e ++ popq r12
    ++ cmpq (imm 0) !%r12
    ++ je label_done ++ compile_stmt s3 ++ compile_stmt s2 ++ jmp label_do ++ label label_done

(* Instanceof *)

let compile_instanceof : (Ast.expr -> X86_64.text) -> Ast.expr -> string -> X86_64.text =
  let cpt = ref ~-1 in
  fun compile_expr e s ->
    incr cpt;
    let label_false = Format.sprintf "instanceof_false_%d" !cpt in
    let label_true = Format.sprintf "instanceof_true_%d" !cpt in
    let label_loop = Format.sprintf "instanceof_loop_%d" !cpt in
    let label_done = Format.sprintf "instanceof_done_%d" !cpt in

    compile_expr e ++ popq r12
    ++ cmpq (imm 0) !%r12
    ++ je label_false ++ label label_loop
    ++ movq (ind r12) !%r12
    ++ cmpq (ilab @@ Format.sprintf "C_%s" s) !%r12
    ++ je label_true
    ++ cmpq (get_ilab_class class_Object) !%r12
    ++ je label_false ++ jmp label_loop ++ label label_false
    ++ pushq (imm 0)
    ++ jmp label_done ++ label label_true
    ++ pushq (imm 1)
    ++ label label_done

(* Cast *)

let compile_cast : (Ast.expr -> X86_64.text) -> Ast.class_ -> Ast.expr -> X86_64.text =
  let cpt = ref ~-1 in
  fun compile_expr cls e ->
    incr cpt;
    let label_exit = Format.sprintf "cast_exit_%d" !cpt in
    let label_done = Format.sprintf "cast_done_%d" !cpt in
    let label_loop = Format.sprintf "cast_loop_%d" !cpt in

    compile_expr e ++ popq r12
    ++ cmpq (imm 0) !%r12
    ++ je label_done ++ label label_loop
    ++ movq (ind r12) !%r12
    ++ cmpq (ilab @@ Format.sprintf "C_%s" cls.class_name) !%r12
    ++ je label_done
    ++ cmpq (get_ilab_class class_Object) !%r12
    ++ je label_exit ++ jmp label_loop ++ label label_exit ++ call label_exit ++ label label_done

(* Local variables *)

let compile_locals (stmt : Ast.stmt) : X86_64.text =
  let cpt = ref 0 in

  let rec loop = function
    | Svar (var, _) ->
      if var.var_ofs = -1 then begin
        cpt := !cpt + 8;
        var.var_ofs <- - !cpt
      end
    | Sif (_, s1, s2) ->
      loop s1;
      loop s2
    | Sblock stmts -> List.iter loop stmts
    | Sfor (s1, _, s2, s3) ->
      loop s1;
      loop s2;
      loop s3
    | _ -> ()
  in

  loop stmt;
  subq (imm !cpt) !%rsp

(* Compile method *)

let compile_method (compile_stmt : Ast.stmt -> X86_64.text) (cls : Ast.class_) (meth : Ast.method_)
  (stmt : Ast.stmt) : X86_64.text =
  set_params_offset meth.meth_params;

  let meth_label = get_label_meth cls meth in
  let save_rbp = pushq !%rbp ++ movq !%rsp !%rbp in
  let local_vars = compile_locals stmt in
  let body = compile_stmt stmt in
  let restore_rbp_and_return =
    if have_return stmt then nop else movq !%rbp !%rsp ++ popq rbp ++ ret
  in

  meth_label ++ save_rbp ++ local_vars ++ body ++ restore_rbp_and_return

(* Printf *)

let compile_printf : X86_64.text =
  label label_print_function ++ pushq !%rbp ++ movq !%rsp !%rbp
  ++ andq (imm ~-16) !%rsp
  ++ movq !%rdi !%rsi
  ++ movq (ilab label_print_data) !%rdi
  ++ xorq !%rax !%rax ++ call "printf" ++ movq !%rbp !%rsp ++ popq rbp ++ ret

(* Malloc *)

let compile_malloc : X86_64.text =
  label label_malloc_function ++ pushq !%rbp ++ movq !%rsp !%rbp
  ++ andq (imm ~-16) !%rsp
  ++ call "malloc" ++ movq !%rbp !%rsp ++ popq rbp ++ ret

(* Strcmp *)

let compile_strcmp : X86_64.text =
  let label = label label_strcmp_function in
  let push_alig = pushq !%rbp ++ movq !%rsp !%rbp ++ andq (imm ~-16) !%rsp in
  let calc = call "strcmp" ++ cmpq (imm 0) !%rax ++ sete !%al ++ movzbq !%al rax in
  let pop_alig = movq !%rbp !%rsp ++ popq rbp in
  let ret = ret in

  label ++ push_alig ++ calc ++ pop_alig ++ ret

(* String_of_int *)

let compile_string_of_int : X86_64.text =
  label label_string_of_int_function
  ++ pushq !%rbp ++ movq !%rsp !%rbp
  ++ andq (imm ~-16) !%rsp
  ++ movq !%rsi !%rdx
  ++ movq (ilab label_string_of_int_data) !%rsi
  ++ xorq !%rax !%rax ++ call "sprintf" ++ movq !%rbp !%rsp ++ popq rbp ++ ret

(* Strlen *)

let compile_strlen : X86_64.text =
  label label_strlen_function ++ pushq !%rbp ++ movq !%rsp !%rbp
  ++ andq (imm ~-16) !%rsp
  ++ call "strlen" ++ movq !%rbp !%rsp ++ popq rbp ++ ret

(* Strcpy *)

let compile_strcpy : X86_64.text =
  label label_strcpy_function ++ pushq !%rbp ++ movq !%rsp !%rbp
  ++ andq (imm ~-16) !%rsp
  ++ call "strcpy" ++ movq !%rbp !%rsp ++ popq rbp ++ ret

(* Strcat *)

let compile_strcat : X86_64.text =
  label label_strcat_function ++ pushq !%rbp ++ movq !%rsp !%rbp
  ++ andq (imm ~-16) !%rsp
  ++ call "strcat" ++ movq !%rbp !%rsp ++ popq rbp ++ ret

(* Exit *)

let compile_exit : X86_64.text =
  label label_exit_function ++ pushq !%rbp ++ movq !%rsp !%rbp
  ++ andq (imm ~-16) !%rsp
  ++ movq (imm 1) !%rdi
  ++ call "exit" ++ movq !%rbp !%rsp ++ popq rbp ++ ret
