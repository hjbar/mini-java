(* Import *)

open X86_64
open Ast
open Compile_utils
open Compile_algo

(* Data *)

let data_queue : data_queue = Queue.create ()

(* Descriptors *)

let descriptors : (string, data) Hashtbl.t = Hashtbl.create 16

(* Label *)

(* Compile descriptors *)

let get_class_descriptor (class_ : class_) : data =
  let label = get_label_class class_ in
  let parent_name = "C_" ^ class_.class_extends.class_name in
  let methods = get_ordered_methods class_ in
  let methods = List.fold_left (fun acc meth -> acc ++ address [ meth ]) nop methods in
  label ++ address [ parent_name ] ++ methods

let compile_class_descriptors (classes : tfile) : unit =
  List.iter
    begin
      fun (cls, _) ->
        let descriptor = get_class_descriptor cls in
        Hashtbl.add descriptors cls.class_name descriptor
    end
    classes

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
    compile_expr e1 ++ compile_expr e2 ++ popq r11 ++ popq r10
    ++
    match op with
    | Badd -> addq !%r11 !%r10 ++ pushq !%r10
    | Bsub -> subq !%r11 !%r10 ++ pushq !%r10
    | Bmul -> imulq !%r11 !%r10 ++ pushq !%r10
    | Bdiv -> movq !%r10 !%rax ++ cqto ++ idivq !%r11 ++ pushq !%rax
    | Bmod -> movq !%r10 !%rax ++ cqto ++ idivq !%r11 ++ pushq !%rdx
    | Beq -> cmpq !%r11 !%r10 ++ sete !%al ++ movzbq !%al r10 ++ pushq !%r10
    | Bneq -> cmpq !%r11 !%r10 ++ setne !%al ++ movzbq !%al r10 ++ pushq !%r10
    | Blt -> cmpq !%r11 !%r10 ++ setl !%al ++ movzbq !%al r10 ++ pushq !%r10
    | Ble -> cmpq !%r11 !%r10 ++ setle !%al ++ movzbq !%al r10 ++ pushq !%r10
    | Bgt -> cmpq !%r11 !%r10 ++ setg !%al ++ movzbq !%al r10 ++ pushq !%r10
    | Bge -> cmpq !%r11 !%r10 ++ setge !%al ++ movzbq !%al r10 ++ pushq !%r10
    | Badd_s ->
      let save_strings = movq !%r10 !%r12 ++ movq !%r11 !%r13 in
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

      save_strings ++ len_s1 ++ len_s2 ++ block ++ copy ++ concat ++ string
    | Band | Bor -> assert false
  end
  | Eunop (op, e) -> begin
    compile_expr e ++ popq r10
    ++
    match op with
    | Uneg -> negq !%r10 ++ pushq !%r10
    | Unot -> xorq (imm 1) !%r10 ++ pushq !%r10
    | Ustring_of_int ->
      let save_int = movq !%r10 !%r12 in
      let block = movq (imm 16) !%rdi ++ call label_malloc_function ++ movq !%rax !%r13 in
      let sprintf =
        movq !%r13 !%rdi
        ++ addq (imm 8) !%rdi
        ++ movq !%r12 !%rsi ++ call label_string_of_int_function
      in
      let string = movq (get_ilab_class class_String) (ind r13) ++ pushq !%r13 in

      save_int ++ block ++ sprintf ++ string
  end
  | Ethis -> debug_text "this" @@ pushq (ind ~ofs:16 rbp)
  | Enull -> pushq @@ imm 0
  | Evar var ->
    Format.printf "accesing var %s at offset %d\n" var.var_name var.var_ofs;

    debug_text "var" @@ pushq (ind ~ofs:var.var_ofs rbp)
  | Eassign_var (var, e) ->
    Format.printf "assign var %s at offset %d\n" var.var_name var.var_ofs;

    debug_text "assign_var"
      (compile_expr e ++ popq r10 ++ movq !%r10 (ind ~ofs:var.var_ofs rbp) ++ pushq !%r10)
  | Eattr (e, attr) ->
    Format.printf "accesing attr %s at offset %d\n" attr.attr_name attr.attr_ofs;

    debug_text "attr" (compile_expr e ++ popq r10 ++ pushq (ind ~ofs:attr.attr_ofs r10))
  | Eassign_attr (e1, attr, e2) ->
    Format.printf "assign attr %s at offset %d\n" attr.attr_name attr.attr_ofs;

    debug_text "assign_attr"
    @@ compile_expr e1 ++ compile_expr e2 ++ popq r11 ++ popq r10
       ++ movq !%r11 (ind ~ofs:attr.attr_ofs r10)
       ++ pushq !%r11
  | Enew (cls, exprs) ->
    let space = 8 * (List.length exprs + 1) in

    let malloc = movq (imm (8 * (get_nb_attribute cls + 1))) !%rdi ++ call label_malloc_function in
    let set_descriptor = movq (get_ilab_class cls) (ind rax) in
    let save_obj = pushq !%rax in

    let params = List.fold_left (fun acc expr -> compile_expr expr ++ acc) nop exprs in

    let push_obj = pushq (ind ~ofs:(space - 8) rsp) in

    let call_constr = call @@ get_name_constr cls in
    let depile = addq (imm space) !%rsp in

    debug_text "new"
      (malloc ++ set_descriptor ++ save_obj ++ params ++ push_obj ++ call_constr ++ depile)
  | Ecall (e, meth, exprs) ->
    let params = List.fold_left (fun acc expr -> compile_expr expr ++ acc) nop exprs in

    let this = compile_expr e in
    let get_class = movq (ind rsp) !%r10 in

    let call = movq (ind r10) !%r11 ++ call_star (ind ~ofs:meth.meth_ofs r11) in
    let depile = addq (imm (8 * (List.length exprs + 1))) !%rsp in

    let ret_val = pushq !%rax in

    debug_text "call" (params ++ this ++ get_class ++ call ++ depile ++ ret_val)
  | Ecast (cls, e) -> failwith "Ecast cls e TODO"
  | Einstanceof (e, s) ->
    failwith
      "Einstanceof e s TODO" (* debug_text "instanceof" @@ compile_instanceof compile_expr e s *)
  | Eprint expr ->
    compile_expr expr ++ popq rdi ++ addq (imm 8) !%rdi ++ call label_print_function ++ pushq !%rax

(* Compile stmt *)

and compile_stmt : stmt -> text = function
  | Sexpr expr -> compile_expr expr ++ comment "Je suis CE soffretu :" ++ popq r10
  | Svar (var, e) ->
    debug_text "Svar" (compile_expr e ++ popq r10 ++ movq !%r10 (ind ~ofs:var.var_ofs rbp))
  | Sif (e, s1, s2) -> compile_if compile_expr compile_stmt e s1 s2
  | Sreturn (Some e) ->
    debug_text "return"
      (compile_expr e ++ popq r10 ++ movq !%r10 !%rax ++ movq !%rbp !%rsp ++ popq rbp ++ ret)
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
  compile_class_descriptors p;
  List.fold_left (fun acc class_ -> acc ++ compile_class class_) nop p

(* Compile data *)

let compile_static_data () : data =
  label label_print_data ++ string "%s" ++ label label_string_of_int_data ++ string "%d"
  ++ Queue.fold
       (fun acc (label_name, str) ->
         acc ++ label label_name ++ address [ "C_" ^ class_String.class_name ] ++ string str )
       nop data_queue

let compile_data () : data = compile_static_data () ++ get_descriptors descriptors

(* Compile build-in function *)

let compile_build_in () =
  compile_printf () ++ compile_malloc () ++ compile_strcmp () ++ compile_string_of_int ()
  ++ compile_strlen () ++ compile_strcpy () ++ compile_strcat ()

let compile_main (p : tfile) =
  globl "main" ++ label "main" ++ call label_main ++ xorq !%rax !%rax ++ ret ++ compile_classes p
  ++ compile_build_in ()

(* Main *)

let file ?debug:(b = false) (p : tfile) : program =
  debug := b;

  let text = compile_main p in
  let data = compile_data () in

  { text; data }
