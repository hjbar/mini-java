(* Import *)

open Format
open X86_64
open Ast
open Compile_utils
open Compile_algo

(* Data *)

let data_queue : data_queue = init_data_queue ()

(* Compile expr *)

let rec compile_expr (e : expr) : text =
  match e.expr_desc with
  | Econstant (Cstring s as cst) ->
    Queue.push (get_label_data (), cst) data_queue;
    nop
  | Eprint expr ->
    let label = new_label_data () in
    compile_expr expr ++ movq (ilab label) !%rdi ++ call label_print_function
  | _ -> failwith "Others expr todo"

(* Compile stmt *)

let rec compile_stmt : stmt -> text = function
  | Sexpr expr -> compile_expr expr
  | Sblock stmts -> compile_stmts stmts
  | _ -> failwith "Others stmt todo"

and compile_stmts (stmts : stmt list) =
  List.fold_left (fun acc stmt -> acc ++ compile_stmt stmt) nop stmts

(* Compile decl *)

let compile_decl (cls : class_) : decl -> text = function
  | Dconstructor (vars, stmt) -> failwith "Dconstructor todo"
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
  Queue.fold
    begin
      fun acc (label_name, cst) ->
        acc ++ label label_name
        ++
        match cst with
        | Cstring s -> string s
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
