(* Import *)

open X86_64
open Ast

(* Debug *)

let debug = ref false

(* Label *)

let label_main = "M_Main_main"

let get_label_meth cls meth = Format.sprintf "M_%s_%s" cls.class_name meth.meth_name |> label

let get_label_cons cls cons = Format.sprintf "C_%s_%s" cls.class_name cons.meth_name |> label
