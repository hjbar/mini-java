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

(* Methods for descriptors *)

let get_methods (class_ : class_) : (string * method_) list =
  let ofs = ref 8 in
  let rec aux class_ =
    let c_name = class_.class_name in
    match c_name with
    | "Object" -> []
    | _ ->
      aux class_.class_extends
      |> List.append
           begin
             Hashtbl.fold
               begin
                 fun _ k acc ->
                   if k.meth_ofs = -1 then begin
                     k.meth_ofs <- !ofs;
                     ofs := !ofs + 8
                   end
                   else ofs := k.meth_ofs + 8;
                   (c_name, k) :: acc
               end
               class_.class_methods []
           end
  in
  aux class_

let get_ordered_methods (class_ : class_) : string list =
  let ord_meth_list =
    get_methods class_ |> List.sort (fun (_, a) (_, b) -> compare a.meth_ofs b.meth_ofs)
  in
  List.map (fun (c_name, meth) -> "M_" ^ c_name ^ "_" ^ meth.meth_name) ord_meth_list

(* And *)

let compile_and : (Ast.expr -> X86_64.text) -> Ast.expr -> Ast.expr -> X86_64.text =
  let cpt = ref ~-1 in
  fun compile_expr e1 e2 ->
    incr cpt;
    let label_done = Format.sprintf "and_done_%d" !cpt in

    compile_expr e1 ++ popq r10
    ++ cmpq (imm 0) !%r10
    ++ je label_done ++ compile_expr e2 ++ popq r10 ++ label label_done ++ pushq !%r10

(* Or *)

let compile_or : (Ast.expr -> X86_64.text) -> Ast.expr -> Ast.expr -> X86_64.text =
  let cpt = ref ~-1 in
  fun compile_expr e1 e2 ->
    incr cpt;
    let label_done = Format.sprintf "or_done_%d" !cpt in

    compile_expr e1 ++ popq r10
    ++ cmpq (imm 1) !%r10
    ++ je label_done ++ compile_expr e2 ++ popq r10 ++ label label_done ++ pushq !%r10

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

    compile_stmt s1 ++ label label_do ++ compile_expr e ++ popq r10
    ++ cmpq (imm 0) !%r10
    ++ je label_done ++ compile_stmt s3 ++ compile_stmt s2 ++ jmp label_do ++ label label_done

(* Attributes *)

let init_attribute_offset (cls : class_) : unit =
  let offset = ref 8 in

  let rec loop cls =
    if cls.class_name = "Object" then ()
    else begin
      loop cls.class_extends;

      List.iter
        begin
          fun attr ->
            if attr.attr_ofs = -1 then begin
              attr.attr_ofs <- !offset;
              offset := !offset + 8
            end
            else offset := attr.attr_ofs + 8
        end
        (cls.class_attributes |> Hashtbl.to_seq_values |> List.of_seq |> List.sort compare)
    end
  in

  loop cls

let print_attr_offset cls =
  Printf.printf "printing attributes offset for class %s\n" cls.class_name;
  let rec loop cls =
    if cls.class_name = "Object" then ()
    else begin
      loop cls.class_extends;
      Printf.printf "length of attributes for class %s : %d\n" cls.class_name
        (Hashtbl.length cls.class_attributes);
      Hashtbl.iter
        begin
          fun _ attr -> Printf.printf "attr %s : %d\n" attr.attr_name attr.attr_ofs
        end
        cls.class_attributes;
      Printf.printf "fin\n"
    end
  in
  loop cls

(* Local variables *)

let compile_locals (stmt : Ast.stmt) : X86_64.text =
  let cpt = ref 0 in

  let rec loop = function
    | Svar (var, _) ->
      cpt := !cpt + 8;
      var.var_ofs <- - !cpt
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

(* Params *)

let set_params_offset (params : var list) : unit =
  let offset = ref 24 in

  List.iter
    begin
      fun param ->
        param.var_ofs <- !offset;
        offset := !offset + 8
    end
    params

(* Compile method *)

let compile_method (compile_stmt : stmt -> text) (cls : class_) (meth : method_) (stmt : stmt) :
  text =
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

let compile_printf () : text =
  label label_print_function ++ pushq !%rbp ++ movq !%rsp !%rbp
  ++ andq (imm ~-16) !%rsp
  ++ movq !%rdi !%rsi
  ++ movq (ilab label_print_data) !%rdi
  ++ xorq !%rax !%rax ++ call "printf" ++ movq !%rbp !%rsp ++ popq rbp ++ ret

(* Malloc *)

let compile_malloc () : text =
  label label_malloc_function ++ pushq !%rbp ++ movq !%rsp !%rbp
  ++ andq (imm ~-16) !%rsp
  ++ call "malloc" ++ movq !%rbp !%rsp ++ popq rbp ++ ret
