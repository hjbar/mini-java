(* Import *)

open Format
open X86_64
open Ast
open Compile_utils
open Compile_algo

(* Data *)

let data_queue : data_queue = Queue.create ()

(* Descriptors *)

let descriptors : (string, data) Hashtbl.t = Hashtbl.create 17

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
    | Bdiv -> movq !%r10 !%rax ++ cqto ++ idivq !%r11 ++ pushq !%rax
    | Bmod -> movq !%r10 !%rax ++ idivq !%r11 ++ pushq !%rdx
    | Beq -> cmpq !%r11 !%r10 ++ sete !%al ++ movzbq !%al r10 ++ pushq !%r10
    | Bneq -> cmpq !%r11 !%r10 ++ setne !%al ++ movzbq !%al r10 ++ pushq !%r10
    | Blt -> cmpq !%r11 !%r10 ++ setl !%al ++ movzbq !%al r10 ++ pushq !%r10
    | Ble -> cmpq !%r11 !%r10 ++ setle !%al ++ movzbq !%al r10 ++ pushq !%r10
    | Bgt -> cmpq !%r11 !%r10 ++ setg !%al ++ movzbq !%al r10 ++ pushq !%r10
    | Bge -> cmpq !%r11 !%r10 ++ setge !%al ++ movzbq !%al r10 ++ pushq !%r10
    | Badd_s -> failwith "Ebinop Badd_s e1 e2 TODO"
    | Band | Bor -> assert false
  end
  | Eunop (op, e) -> begin
    compile_expr e ++ popq r10
    ++
    match op with
    | Uneg -> negq !%r10 ++ pushq !%r10
    | Unot -> xorq (imm 1) !%r10 ++ pushq !%r10
    | Ustring_of_int -> failwith "Eunop Ustring_of_int e TODO"
  end
  | Ethis -> pushq @@ ind ~ofs:~-24 rbp
  | Enull -> pushq (imm 0)
  | Evar var -> pushq (ind ~ofs:(-var.var_ofs) rbp)
  | Eassign_var (var, e) -> compile_expr e ++ popq r10 ++ movq !%r10 (ind ~ofs:(-var.var_ofs) rbp)
  | Eattr (e, attr) -> compile_expr e ++ popq r10 ++ pushq (ind ~ofs:attr.attr_ofs r10)
  | Eassign_attr (e1, attr, e2) ->
    compile_expr e1 ++ compile_expr e2 ++ popq r11 ++ popq r10
    ++ movq !%r11 (ind ~ofs:attr.attr_ofs r10)
  | Enew (cls, exprs) ->
    (* le résultat est stocké dans RAX *)
    init_attribute_offset cls;

    let malloc = movq (imm (8 * (get_nb_attribute cls + 1))) !%rdi ++ call label_malloc_function in
    let set_descriptor = movq (get_ilab_class cls) (ind rax) in
    let push_obj = pushq !%rax in
    let call_constr =
      let obj = make_expr (Evar (make_var "" (Tclass cls) 0)) (Tclass cls) in
      let meth = Hashtbl.find cls.class_methods cls.class_name in
      let expr = make_expr (Ecall (obj, meth, exprs)) Tvoid in
      compile_expr expr
    in

    malloc ++ set_descriptor ++ push_obj ++ call_constr
  | Ecall (e, meth, exprs) ->
    let params = List.fold_left (fun acc expr -> compile_expr expr ++ acc) nop exprs in
    let this = compile_expr e in
    let call = call_star (ind ~ofs:meth.meth_ofs rsp) in

    params ++ this ++ call
  | Ecast (cls, e) -> failwith "Ecast cls e TODO"
  | Einstanceof (e, s) -> failwith "Einstanceof e s TODO"
  | Eprint expr ->
    let label = new_label_data () in
    compile_expr expr ++ movq (ilab label) !%rdi ++ addq (imm 8) !%rdi ++ call label_print_function

(* Compile stmt *)

and compile_stmt : stmt -> text = function
  | Sexpr expr -> compile_expr expr
  | Svar (var, e) -> compile_expr e ++ popq r10 ++ movq !%r10 (ind ~ofs:(-var.var_ofs) rbp)
  | Sif (e, s1, s2) -> compile_if compile_expr compile_stmt e s1 s2
  | Sreturn (Some e) -> compile_expr e ++ ret
  | Sreturn None -> ret
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

let compile_class ((cls, decls) : tclass) : text = compile_decls cls decls

let compile_classes (p : tfile) =
  compile_class_descriptors p;
  List.fold_left (fun acc class_ -> acc ++ compile_class class_) nop p

(* Compile data *)

let compile_static_data () : data =
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

let compile_data () : data = compile_static_data () ++ get_descriptors descriptors

(* Compile build-in function *)

let compile_build_in () = compile_printf () ++ compile_malloc ()

let compile_main (p : tfile) =
  globl "main" ++ label "main" ++ call label_main ++ xorq !%rax !%rax ++ ret ++ compile_classes p
  ++ compile_build_in ()

(* Main *)

let file ?debug:(b = false) (p : tfile) : program =
  debug := b;

  let text = compile_main p in
  let data = compile_data () in

  { text; data }
