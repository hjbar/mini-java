(* Import *)

open Ast
open X86_64
open Compile_algo
open Compile_utils

(* Data *)

let data_queue : data_queue = Queue.create ()

(* Descriptors *)

let descriptors : descriptors = Hashtbl.create 16

(* Compile expr *)

let rec compile_expr (e : expr) : text =
  match e.expr_desc with
  | Econstant (Cbool false) -> pushq @@ imm 0
  | Econstant (Cbool true) -> pushq @@ imm 1
  | Econstant (Cint n) -> pushq @@ imm @@ Int32.to_int n
  | Econstant (Cstring s) -> debug_text "String" @@ compile_string s data_queue
  | Ebinop (Band, e1, e2) -> debug_text "And" @@ compile_and compile_expr e1 e2
  | Ebinop (Bor, e1, e2) -> debug_text "Or" @@ compile_or compile_expr e1 e2
  | Ebinop (Beq, e1, e2) when is_type_string e1 && is_type_string e2 ->
    compile_expr e1 ++ compile_expr e2 ++ popq rsi ++ popq rdi
    ++ addq (imm 8) !%rsi
    ++ addq (imm 8) !%rdi
    ++ call label_strcmp_function ++ pushq !%rax
  | Ebinop (op, e1, e2) -> begin
    compile_expr e1 ++ compile_expr e2 ++ popq r13 ++ popq r12
    ++
    match op with
    | Badd -> addq !%r13 !%r12 ++ pushq !%r12
    | Bsub -> subq !%r13 !%r12 ++ pushq !%r12
    | Bmul -> imulq !%r13 !%r12 ++ pushq !%r12
    | Bdiv -> movq !%r12 !%rax ++ cqto ++ idivq !%r13 ++ pushq !%rax
    | Bmod -> movq !%r12 !%rax ++ cqto ++ idivq !%r13 ++ pushq !%rdx
    | Beq -> cmpq !%r13 !%r12 ++ sete !%al ++ movzbq !%al r12 ++ pushq !%r12
    | Bneq -> cmpq !%r13 !%r12 ++ setne !%al ++ movzbq !%al r12 ++ pushq !%r12
    | Blt -> cmpq !%r13 !%r12 ++ setl !%al ++ movzbq !%al r12 ++ pushq !%r12
    | Ble -> cmpq !%r13 !%r12 ++ setle !%al ++ movzbq !%al r12 ++ pushq !%r12
    | Bgt -> cmpq !%r13 !%r12 ++ setg !%al ++ movzbq !%al r12 ++ pushq !%r12
    | Bge -> cmpq !%r13 !%r12 ++ setge !%al ++ movzbq !%al r12 ++ pushq !%r12
    | Badd_s ->
      let len_s1 =
        movq !%r12 !%rdi ++ addq (imm 8) !%rdi ++ call label_strlen_function ++ movq !%rax !%r14
      in
      let len_s2 =
        movq !%r13 !%rdi ++ addq (imm 8) !%rdi ++ call label_strlen_function ++ movq !%rax !%r15
      in
      let block =
        addq !%r14 !%r15
        ++ addq (imm 9) !%r15
        ++ movq !%r15 !%rdi ++ call label_malloc_function ++ movq !%rax !%r15
      in
      let copy =
        movq !%r15 !%rdi
        ++ addq (imm 8) !%rdi
        ++ movq !%r12 !%rsi
        ++ addq (imm 8) !%rsi
        ++ call label_strcpy_function
      in
      let concat =
        movq !%r15 !%rdi
        ++ addq (imm 8) !%rdi
        ++ movq !%r13 !%rsi
        ++ addq (imm 8) !%rsi
        ++ call label_strcat_function
      in
      let string = movq (get_ilab_class class_String) (ind r15) ++ pushq !%r15 in

      len_s1 ++ len_s2 ++ block ++ copy ++ concat ++ string
    | Band | Bor -> assert false
  end
  | Eunop (op, e) -> begin
    compile_expr e ++ popq r12
    ++
    match op with
    | Uneg -> negq !%r12 ++ pushq !%r12
    | Unot -> xorq (imm 1) !%r12 ++ pushq !%r12
    | Ustring_of_int ->
      let block = movq (imm 16) !%rdi ++ call label_malloc_function ++ movq !%rax !%r13 in
      let sprintf =
        movq !%r13 !%rdi
        ++ addq (imm 8) !%rdi
        ++ movq !%r12 !%rsi ++ call label_string_of_int_function
      in
      let string = movq (get_ilab_class class_String) (ind r13) ++ pushq !%r13 in

      block ++ sprintf ++ string
  end
  | Ethis -> debug_text "this" @@ pushq (ind ~ofs:16 rbp)
  | Enull -> pushq @@ imm 0
  | Evar var -> debug_text "var" @@ pushq (ind ~ofs:var.var_ofs rbp)
  | Eassign_var (var, e) ->
    debug_text "assign_var"
      (compile_expr e ++ popq r12 ++ movq !%r12 (ind ~ofs:var.var_ofs rbp) ++ pushq !%r12)
  | Eattr (e, attr) ->
    debug_text "attr" (compile_expr e ++ popq r12 ++ pushq (ind ~ofs:attr.attr_ofs r12))
  | Eassign_attr (e1, attr, e2) ->
    debug_text "assign_attr"
    @@ compile_expr e1 ++ compile_expr e2 ++ popq r13 ++ popq r12
       ++ movq !%r13 (ind ~ofs:attr.attr_ofs r12)
       ++ pushq !%r13
  | Enew (cls, exprs) ->
    let malloc_space = 8 * (get_nb_attribute cls + 1) in
    let stack_space = 8 * (List.length exprs + 1) in

    let malloc = movq (imm malloc_space) !%rdi ++ call label_malloc_function in
    let set_descriptor = movq (get_ilab_class cls) (ind rax) in
    let save_obj = pushq !%rax in

    let params = List.fold_left (fun acc expr -> compile_expr expr ++ acc) nop exprs in
    let push_obj = pushq (ind ~ofs:(stack_space - 8) rsp) in

    let call_constr = call @@ get_name_constr cls in
    let depile = addq (imm stack_space) !%rsp in

    debug_text "new"
      (malloc ++ set_descriptor ++ save_obj ++ params ++ push_obj ++ call_constr ++ depile)
  | Ecall (e, meth, exprs) ->
    let stack_space = 8 * (List.length exprs + 1) in

    let params = List.fold_left (fun acc expr -> compile_expr expr ++ acc) nop exprs in
    let this = compile_expr e in

    let get_class = movq (ind rsp) !%r12 in
    let call = movq (ind r12) !%r13 ++ call_star (ind ~ofs:meth.meth_ofs r13) in
    let depile = addq (imm stack_space) !%rsp in

    let ret_val = pushq !%rax in

    debug_text "call" (params ++ this ++ get_class ++ call ++ depile ++ ret_val)
  | Ecast (cls, e) -> failwith "Ecast cls e TODO"
  | Einstanceof (e, s) -> debug_text "instanceof" @@ compile_instanceof compile_expr e s
  | Eprint expr ->
    compile_expr expr ++ popq rdi ++ addq (imm 8) !%rdi ++ call label_print_function ++ pushq !%rax

(* Compile stmt *)

and compile_stmt : stmt -> text = function
  | Sexpr expr -> compile_expr expr ++ popq r12
  | Svar (var, e) ->
    debug_text "Svar" (compile_expr e ++ popq r12 ++ movq !%r12 (ind ~ofs:var.var_ofs rbp))
  | Sif (e, s1, s2) -> compile_if compile_expr compile_stmt e s1 s2
  | Sreturn (Some e) ->
    debug_text "return"
      (compile_expr e ++ popq r12 ++ movq !%r12 !%rax ++ movq !%rbp !%rsp ++ popq rbp ++ ret)
  | Sreturn None -> debug_text "return" (movq !%rbp !%rsp ++ popq rbp ++ ret)
  | Sblock stmts -> compile_stmts stmts
  | Sfor (s1, e, s2, s3) -> compile_for compile_expr compile_stmt s1 e s2 s3

and compile_stmts (stmts : stmt list) =
  List.fold_left (fun acc stmt -> acc ++ compile_stmt stmt) nop stmts

(* Compile decl *)

let compile_decl (cls : class_) : decl -> text = function
  | Dconstructor (vars, stmt) ->
    let meth = Hashtbl.find cls.class_methods cls.class_name in
    compile_method compile_stmt cls meth stmt
  | Dmethod (meth, stmt) -> compile_method compile_stmt cls meth stmt

let compile_decls (cls : class_) (decls : decl list) =
  List.fold_left (fun acc decl -> acc ++ compile_decl cls decl) nop decls

(* Compile class *)

let compile_class ((cls, decls) : tclass) : text =
  init_attribute_offset cls;
  compile_decls cls decls

let compile_classes (p : tfile) =
  compile_class_descriptors p descriptors;
  List.fold_left (fun acc class_ -> acc ++ compile_class class_) nop p

(* Compile data *)

let compile_static_data () : data =
  label label_print_data ++ string "%s" ++ label label_string_of_int_data ++ string "%d"
  ++ Queue.fold
       begin
         fun acc (label_name, str) ->
           acc ++ label label_name
           ++ address [ get_descriptor_name class_String.class_name ]
           ++ string str
       end
       nop data_queue

let get_descriptors (descriptors : descriptors) : data =
  Hashtbl.fold (fun _ v acc -> acc ++ v) descriptors nop

let compile_data () : data = compile_static_data () ++ get_descriptors descriptors

(* Compile build-in function *)

let compile_build_in =
  compile_printf ++ compile_malloc ++ compile_strcmp ++ compile_string_of_int ++ compile_strlen
  ++ compile_strcpy ++ compile_strcat

let compile_main (p : tfile) =
  globl "main" ++ label "main" ++ call label_main ++ xorq !%rax !%rax ++ ret ++ compile_classes p
  ++ compile_build_in

(* Main *)

let file ?debug:(b = false) (p : tfile) : program =
  debug := b;

  let text = compile_main p in
  let data = compile_data () in

  { text; data }
