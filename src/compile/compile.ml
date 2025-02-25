(* Import *)

open Format
open X86_64
open Ast
open Compile_utils
open Compile_algo

(* Data *)

let data_queue : data_queue = Queue.create ()

(* Compile expr *)

let rec compile_expr (e : expr) : text =
  match e.expr_desc with
  | Econstant (Cbool false) -> pushq @@ imm 0
  | Econstant (Cbool true) -> pushq @@ imm 1
  | Econstant (Cint n) -> pushq @@ imm @@ Int32.to_int n
  | Econstant (Cstring s as cst) ->
    Queue.push (get_label_data (), cst) data_queue;
    nop
  | Ebinop (Band, e1, e2) -> compile_stmt @@ rewrite_and e1 e2
  | Ebinop (Bor, e1, e2) -> compile_stmt @@ rewrite_or e1 e2
  | Ebinop (op, e1, e2) -> begin
    compile_expr e1 ++ compile_expr e2 ++ popq r11 ++ popq r10
    ++
    match op with
    | Badd -> addq !%r11 !%r10 ++ pushq !%r10
    | Bsub -> subq !%r11 !%r10 ++ pushq !%r10
    | Bmul -> imulq !%r11 !%r10 ++ pushq !%r10
    | Bdiv -> movq !%r10 !%rax ++ idivq !%r11 ++ pushq !%rax
    | Bmod -> movq !%r10 !%rax ++ idivq !%r11 ++ pushq !%rdx
    | Beq ->
      movq !%r10 !%rax ++ movq !%r11 !%rbx ++ cmpq !%rbx !%rax ++ sete !%al ++ movsbq !%al r10
      ++ pushq !%r10
    | Bneq ->
      movq !%r10 !%rax ++ movq !%r11 !%rbx ++ cmpq !%rbx !%rax ++ setne !%al ++ movsbq !%al r10
      ++ pushq !%r10
    | Blt ->
      movq !%r10 !%rax ++ movq !%r11 !%rbx ++ cmpq !%rbx !%rax ++ setl !%al ++ movsbq !%al r10
      ++ pushq !%r10
    | Ble ->
      movq !%r10 !%rax ++ movq !%r11 !%rbx ++ cmpq !%rbx !%rax ++ setle !%al ++ movsbq !%al r10
      ++ pushq !%r10
    | Bgt ->
      movq !%r10 !%rax ++ movq !%r11 !%rbx ++ cmpq !%rbx !%rax ++ setg !%al ++ movsbq !%al r10
      ++ pushq !%r10
    | Bge ->
      movq !%r10 !%rax ++ movq !%r11 !%rbx ++ cmpq !%rbx !%rax ++ setge !%al ++ movsbq !%al r10
      ++ pushq !%r10
    | Badd_s -> failwith "Ebinop Badd_s e1 e2 TODO"
    | Band | Bor -> assert false
  end
  | Eunop (op, e) -> begin
    compile_expr e ++ popq r10
    ++
    match op with
    | Uneg -> negq !%r10 ++ pushq !%r10
    | Unot -> notq !%r10 ++ pushq !%r10
    | Ustring_of_int -> failwith "Eunop Ustring_of_int e TODO"
  end
  | Ethis -> failwith "Ethis TODO"
  | Enull -> pushq (imm 0)
  | Evar var -> failwith "Evar var TODO"
  | Eassign_var (var, e) -> failwith "Eassign_var var e TODO"
  | Eattr (e, attr) -> failwith "Eattr e attr TODO"
  | Eassign_attr (e1, attr, e2) -> failwith "Eassign_attr e1 attr e2"
  | Enew (cls, exprs) -> failwith "Enew cls exprs TODO"
  | Ecall (e, meth, exprs) -> failwith "Ecall e meth exprs TODO"
  | Ecast (cls, e) -> failwith "Ecast cls e TODO"
  | Einstanceof (e, s) -> failwith "Einstanceof e s TODO"
  | Eprint expr ->
    let label = new_label_data () in
    compile_expr expr ++ movq (ilab label) !%rdi ++ addq (imm 8) !%rdi ++ call label_print_function

(* Compile stmt *)

and compile_stmt : stmt -> text = function
  | Sexpr expr -> compile_expr expr
  | Svar (var, e) -> failwith "Svar var e TODO"
  | Sif (e, s1, s2) -> compile_if compile_expr compile_stmt e s1 s2
  | Sreturn (Some e) -> compile_expr e ++ ret
  | Sreturn None -> ret
  | Sblock stmts -> compile_stmts stmts
  | Sfor (s1, e, s2, s3) -> compile_for compile_expr compile_stmt s1 e s2 s3

and compile_stmts (stmts : stmt list) =
  List.fold_left (fun acc stmt -> acc ++ compile_stmt stmt) nop stmts

(* Compile decl *)

let compile_decl (cls : class_) : decl -> text = function
  | Dconstructor (vars, stmt) -> failwith "Dconstructor vars stmt todo"
  | Dmethod (meth, stmt) ->
    get_label_meth cls meth ++ compile_stmt stmt ++ if is_type_void meth.meth_type then ret else nop

let compile_decls (cls : class_) (decls : decl list) =
  List.fold_left (fun acc decl -> acc ++ compile_decl cls decl) nop decls

(* Compile class *)

let compile_class ((cls, decls) : tclass) : text = compile_decls cls decls

let compile_classes (p : tfile) =
  List.fold_left (fun acc class_ -> acc ++ compile_class class_) nop p

(* Compile data *)

let compile_data () : data =
  label label_print_data ++ string "%s"
  ++ Queue.fold
       begin
         fun acc (label_name, cst) ->
           acc ++ label label_name
           ++
           match cst with
           | Cstring s -> dquad [ 0 ] ++ string s
           | _ -> failwith "more cst in match in compile_data TODO"
       end
       nop data_queue

(* Compile build-in function *)

let compile_build_in () = compile_printf ()

let compile_main (p : tfile) =
  globl "main" ++ label "main" ++ call label_main ++ xorq !%rax !%rax ++ ret ++ compile_classes p
  ++ compile_build_in ()

(* Main *)

let file ?debug:(b = false) (p : tfile) : program =
  debug := b;

  let text = compile_main p in
  let data = compile_data () in

  { text; data }
