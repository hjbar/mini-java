(* Import *)

open Ast
open X86_64

(* Debug *)

let debug = ref false

let debug_text case text =
  if !debug then
    comment ""
    ++ comment (" Début " ^ case ^ " :")
    ++ comment "" ++ text ++ comment ""
    ++ comment (" Fin " ^ case ^ " :")
    ++ comment ""
  else text

(* Label *)

let label_print_function = "M_print_string"

let label_malloc_function = "M_malloc"

let label_strcmp_function = "M_strcmp"

let label_string_of_int_function = "M_string_of_int"

let label_strlen_function = "M_strlen"

let label_strcpy_function = "M_strcpy"

let label_strcat_function = "M_strcat"

let label_print_data = ".D_print_string"

let label_string_of_int_data = ".D_string_of_int"

let label_main = "M_Main_main"

let get_label_meth cls meth = Format.sprintf "M_%s_%s" cls.class_name meth.meth_name |> label

let get_name_constr cls = Format.sprintf "M_%s_%s" cls.class_name cls.class_name

let get_label_class cls = Format.sprintf "C_%s" cls.class_name |> label

let get_ilab_class cls = Format.sprintf "C_%s" cls.class_name |> ilab

let get_descriptor_name s = Format.sprintf "C_%s" s

(* Type_def *)

type data_queue = (string * string) Queue.t

type descriptors = (string, data) Hashtbl.t

(* Type *)

let is_type_void = function Tvoid -> true | _ -> false

let is_type_string e =
  match e.expr_type with Tclass cls when cls.class_name = "String" -> true | _ -> false

(* Build-in classes *)

let class_String = Typing_utils.class_String

(* Methods for descriptors *)

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

let update_method_list old_methods new_methods =
  let old_method_map =
    List.fold_left
      (fun acc (_, m) -> StringMap.add m.meth_name m.meth_ofs acc)
      StringMap.empty old_methods
  in
  List.iter
    begin
      fun (_, m) ->
        match StringMap.find_opt m.meth_name old_method_map with
        | Some old_offset -> m.meth_ofs <- old_offset
        | None -> ()
    end
    new_methods;

  let new_method_names =
    List.fold_left (fun acc (_, m) -> StringSet.add m.meth_name acc) StringSet.empty new_methods
  in

  let filtered_old_methods =
    List.filter (fun (_, m) -> not @@ StringSet.mem m.meth_name new_method_names) old_methods
  in

  filtered_old_methods @ new_methods

let get_methods class_ =
  let ofs = ref 8 in

  let rec aux class_ =
    let c_name = class_.class_name in

    match c_name with
    | "Object" -> []
    | _ ->
      let nl = aux class_.class_extends in

      let sl =
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

      update_method_list nl sl
  in

  aux class_

let get_ordered_methods class_ =
  let ord_meth_list =
    get_methods class_ |> List.sort (fun (_, a) (_, b) -> compare a.meth_ofs b.meth_ofs)
  in

  List.map (fun (c_name, meth) -> "M_" ^ c_name ^ "_" ^ meth.meth_name) ord_meth_list

(* Compile descriptors *)

let get_class_descriptor class_ =
  let label = get_label_class class_ in
  let parent_name = get_descriptor_name class_.class_extends.class_name in
  let methods = get_ordered_methods class_ in
  let methods = List.fold_left (fun acc meth -> acc ++ address [ meth ]) nop methods in
  label ++ address [ parent_name ] ++ methods

let compile_class_descriptors classes descriptors =
  List.iter
    begin
      fun (cls, _) ->
        let descriptor = get_class_descriptor cls in
        Hashtbl.replace descriptors cls.class_name descriptor
    end
    classes

(* Attributes *)

let get_nb_attribute cls =
  let rec loop cls cpt =
    if cls.class_name = "Object" then cpt
    else loop cls.class_extends (cpt + Hashtbl.length cls.class_attributes)
  in
  loop cls 0

let init_attribute_offset cls =
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

(* Params *)

let set_params_offset params =
  let offset = ref 24 in

  List.iter
    begin
      fun param ->
        param.var_ofs <- !offset;
        offset := !offset + 8
    end
    params

(* Return *)

let rec have_return = function
  | Sreturn _ -> true
  | Sif (_, s1, s2) -> have_return s1 && have_return s2
  | Sblock block -> List.exists have_return block
  | _ -> false
