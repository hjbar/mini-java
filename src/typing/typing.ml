(* Import *)

open Ast
open Typing_utils
open Typing_algo

(* Globals of typing *)

let current_class = ref class_Object

let current_return_type = ref Tnull

let classes : classes = init_classes_env ()

(* Typing expr *)

let rec print_pexpr_desc (p : pexpr_desc) =
  match p with
  | PEconstant c -> Printf.printf "PEconstant \n"
  | PEbinop (b, e1, e2) -> Printf.printf "PEbinop \n"
  | PEunop (u, e) -> Printf.printf "PEunop \n"
  | PEthis -> Printf.printf "PEthis \n"
  | PEnull -> Printf.printf "PEnull \n"
  | PEident i -> Printf.printf "PEident \n"
  | PEdot (e, i) -> Printf.printf "PEdot \n"
  | PEassign_ident (i, e) -> Printf.printf "PEassign_ident \n"
  | PEassign_dot (e, i, e2) -> Printf.printf "PEassign_dot \n"
  | PEnew (i, l) -> Printf.printf "PEnew \n"
  | PEcall (e, i, l) -> Printf.printf "PEcall \n"
  | PEcast (t, e) -> Printf.printf "PEcast \n"
  | PEinstanceof (e, t) -> Printf.printf "PEinstanceof \n"

let rec print_stmt_desc (p : pstmt_desc) =
  match p with
  | PSexpr e -> Printf.printf "PSexpr \n"
  | PSvar (t, i, e) -> Printf.printf "PSvar \n"
  | PSif (e, s1, s2) -> Printf.printf "PSif \n"
  | PSreturn e -> Printf.printf "PSreturn \n"
  | PSblock l -> Printf.printf "PSblock \n"
  | PSfor (s1, e, s2, s3) -> Printf.printf "PSfor \n"

let rec type_expr (env : typing_env) (expr : pexpr) : expr =
  let loc = expr.pexpr_loc in
  (* print_pexpr_desc expr.pexpr_desc; *)

  match expr.pexpr_desc with
  | PEconstant cst -> make_expr (Econstant cst) (cst_to_typ cst)
  | PEbinop (op, e1, e2) -> begin
    let loc1 = e1.pexpr_loc in
    let loc2 = e2.pexpr_loc in

    let e1 = type_expr env e1 in
    let e2 = type_expr env e2 in

    match op with
    | Beq | Bneq ->
      (* TODO: remplacer par le sous-typage *)
      if e1.expr_type <>* Tnull && e2.expr_type <>* Tnull then
        check_type ~loc e1.expr_type e2.expr_type;
      make_expr (Ebinop (op, e1, e2)) Tboolean
    | Blt | Ble | Bgt | Bge ->
      check_type ~loc:loc1 Tint e1.expr_type;
      check_type ~loc:loc2 Tint e2.expr_type;
      make_expr (Ebinop (op, e1, e2)) Tboolean
    | Bsub | Bmul | Bdiv | Bmod ->
      check_type ~loc:loc1 Tint e1.expr_type;
      check_type ~loc:loc2 Tint e2.expr_type;
      make_expr (Ebinop (op, e1, e2)) Tint
    | Band | Bor ->
      check_type ~loc:loc1 Tboolean e1.expr_type;
      check_type ~loc:loc2 Tboolean e2.expr_type;
      make_expr (Ebinop (op, e1, e2)) Tboolean
    | Badd -> type_add ~loc e1 e2
    | Badd_s -> assert false
  end
  | PEunop (op, e) -> begin
    let loc_e = e.pexpr_loc in
    let e = type_expr env e in

    match op with
    | Uneg ->
      check_type ~loc:loc_e Tint e.expr_type;
      make_expr (Eunop (Uneg, e)) Tint
    | Unot ->
      check_type ~loc:loc_e Tboolean e.expr_type;
      make_expr (Eunop (Unot, e)) Tboolean
    | Ustring_of_int -> assert false
  end
  | PEthis ->
    let c = !current_class in

    check_exist_class ~loc classes c;

    make_expr Ethis (Tclass c)
  | PEnull -> make_expr Enull Tnull
  | PEident var when Env.mem var.id env ->
    let typ = Env.find var.id env in
    let expr = make_var var.id typ ~-1 in

    make_expr (Evar expr) typ
  | PEident var (* Not in env *) ->
    let cls = !current_class in
    check_has_attribute ~loc:var.loc var.id cls;

    let typ = (get_attribute var.id cls).attr_type in
    let expr = make_var var.id typ ~-1 in

    make_expr (Evar expr) typ
  | PEdot (c, field) ->
    let e = type_expr env c in
    check_is_class ~loc:c.pexpr_loc e.expr_type;

    let cls = get_class_type e.expr_type in
    check_has_attribute ~loc:field.loc field.id cls;

    let attr = get_attribute field.id cls in

    make_expr (Eattr (e, attr)) attr.attr_type
  | PEassign_ident (var, e) when Env.mem var.id env ->
    let typ = Env.find var.id env in

    (* TODO: utiliser le sous-typage *)
    let typed_e = type_expr env e in
    if typed_e.expr_type <>* Tnull then check_type ~loc:e.pexpr_loc typ typed_e.expr_type;

    let expr = make_var var.id typ ~-1 in
    make_expr (Eassign_var (expr, typed_e)) typ
  | PEassign_ident (var, e) (* Not in env *) ->
    let cls = !current_class in
    check_has_attribute ~loc:var.loc var.id cls;

    let typ = (get_attribute var.id cls).attr_type in

    (* TODO: utiliser le sous-typage *)
    let typed_e = type_expr env e in
    if typed_e.expr_type <>* Tnull then check_type ~loc:e.pexpr_loc typ typed_e.expr_type;

    let expr = make_var var.id typ ~-1 in
    make_expr (Eassign_var (expr, typed_e)) typ
  | PEassign_dot (c, field, e) ->
    let e1 = type_expr env c in
    check_is_class ~loc:c.pexpr_loc e1.expr_type;

    let cls = get_class_type e1.expr_type in
    check_has_attribute ~loc:field.loc field.id cls;

    let attr = get_attribute field.id cls in

    (* TODO: utiliser le sous-typage *)
    let e2 = type_expr env e in
    if e2.expr_type <>* Tnull then check_type ~loc:e.pexpr_loc attr.attr_type e2.expr_type;

    make_expr (Eassign_attr (e1, attr, e2)) attr.attr_type
  | PEnew (name, args) ->
    let cls = Hashtbl.find classes name.id in
    let constr = get_method name.id name.loc args !cls in

    (* TODO : utiliser le sous-typage *)
    let typed_args = type_call_args type_expr env args constr.meth_params in

    make_expr (Enew (!cls, typed_args)) constr.meth_type
  | PEcall (c, name, args) ->
    if name.id = "print" && is_system_out c then begin
      let expr = get_argument ~loc:name.loc name.id args in
      let typed_e = type_expr env expr in

      check_type ~loc:expr.pexpr_loc type_string typed_e.expr_type;

      make_expr (Eprint typed_e) Tvoid
    end
    else begin
      let typed_c = type_expr env c in

      if name.id = "equals" && typed_c.expr_type =* type_string then begin
        let e1 = get_argument ~loc:name.loc name.id args in
        check_type ~loc:c.pexpr_loc type_string typed_c.expr_type;

        let typed_e1 = type_expr env e1 in
        check_type ~loc:e1.pexpr_loc type_string typed_e1.expr_type;

        make_expr (Ebinop (Beq, typed_e1, typed_c)) Tboolean
      end
      else begin
        let cls = get_class_type typed_c.expr_type in
        let meth = get_method name.id name.loc args cls in

        (* TODO : utiliser le sous-typage *)
        let typed_args = type_call_args type_expr env args meth.meth_params in

        make_expr (Ecall (typed_c, meth, typed_args)) meth.meth_type
      end
    end
  | PEcast (typ, e) ->
    let typed_e = type_expr env e in
    let typ = get_typ classes typ in
    (* TODO: utiliser le sous-typage *)
    check_type ~loc:e.pexpr_loc typ typed_e.expr_type;

    check_is_class ~loc typ;
    make_expr (Ecast (get_class_type typ, typed_e)) typ
  | PEinstanceof (e, typ) ->
    let typed_e = type_expr env e in
    let typ = get_typ classes typ in
    check_is_class_or_null ~loc typ;

    (* TODO: utiliser le sous-typage *)
    check_type ~loc:e.pexpr_loc typ typed_e.expr_type;
    make_expr (Einstanceof (typed_e, (get_class_type typ).class_name)) Tboolean

and type_exprs (env : typing_env) (exprs : pexpr list) : expr list = List.map (type_expr env) exprs

(* Typing stmt *)

let rec type_stmt (env : typing_env) (stmt : pstmt) : typing_env * stmt =
  let loc = stmt.pstmt_loc in

  (* print_stmt_desc stmt.pstmt_desc; *)
  match stmt.pstmt_desc with
  | PSexpr e -> (env, Sexpr (type_expr env e))
  | PSvar (typ, var, None) when not @@ Env.mem var.id env ->
    let typ = get_typ classes typ in
    let env = Env.add var.id typ env in

    (env, Svar (make_var var.id typ ~-1, make_expr Enull typ))
  | PSvar (typ, var, Some e) when not @@ Env.mem var.id env ->
    let typ = get_typ classes typ in
    let env = Env.add var.id typ env in

    let typed_e = type_expr env e in
    if typed_e.expr_type <>* Tnull then check_type ~loc:e.pexpr_loc typ typed_e.expr_type;

    (env, Svar (make_var var.id typ ~-1, make_expr typed_e.expr_desc typed_e.expr_type))
  | PSvar (_, var, _) -> error ~loc:var.loc "The variable %s is already defined" var.id
  | PSif (e, s1, s2) ->
    let typed_e = type_expr env e in

    check_type ~loc:e.pexpr_loc Tboolean typed_e.expr_type;

    let typed_s1 = type_stmt env s1 |> snd in
    let typed_s2 = type_stmt env s2 |> snd in

    (env, Sif (typed_e, typed_s1, typed_s2))
  | PSreturn None ->
    check_type ~loc Tvoid !current_return_type;
    (env, Sreturn None)
  | PSreturn (Some expr) ->
    let expr = type_expr env expr in
    check_type ~loc !current_return_type expr.expr_type;
    (env, Sreturn (Some expr))
  | PSblock block -> (env, Sblock (type_stmts env block))
  | PSfor (s1, e, s2, s3) ->
    let env, typed_s1 = type_stmt env s1 in

    let typed_e = type_expr env e in
    check_type ~loc:e.pexpr_loc Tboolean typed_e.expr_type;

    let env, typed_s2 = type_stmt env s2 in
    let _, typed_s3 = type_stmt env s3 in

    (env, Sfor (typed_s1, typed_e, typed_s2, typed_s3))

and type_stmts (env : typing_env) (stmts : pstmt list) : stmt list =
  stmts
  |> List.fold_left
       begin
         fun (env, acc) stmt ->
           let env, typed_stmt = type_stmt env stmt in
           (env, typed_stmt :: acc)
       end
       (env, [])
  |> snd |> List.rev

(* Typing decl *)

let type_decl : pdecl -> decl = function
  | PDattribute _ -> assert false
  | PDconstructor (name, params, block) ->
    verify_have_not_return block.pstmt_loc name.id block.pstmt_desc;

    let vars, env = env_from_params classes params in
    let block = type_stmt env block |> snd in
    Dconstructor (vars, block)
  | PDmethod (typ_opt, name, params, block) ->
    let typ = get_typ_opt classes typ_opt in

    if typ <> Tvoid then verify_have_return block.pstmt_loc name.id block.pstmt_desc;
    current_return_type := typ;

    let vars, env = env_from_params classes params in
    let m = make_method name.id typ vars ~-1 in
    let block = type_stmt env block |> snd in
    Dmethod (m, block)

let type_decls (decls : pdecl list) : decl list =
  List.fold_left
    (fun acc decl -> match decl with PDattribute _ -> acc | _ -> type_decl decl :: acc)
    [] decls
  |> List.rev

(* Typing class *)

let type_class ((id, _parent, decls) : pclass) : tclass =
  current_class := !(Hashtbl.find classes id.id);
  (!(Hashtbl.find classes id.id), type_decls decls)

let type_classes (p : pfile) : tfile = List.map type_class p

(* Main *)

let file ?debug:(b = false) (p : pfile) : tfile =
  (* TODO : extends todo in update_class *)
  debug := b;

  init_classes classes p;
  update_classes classes p;
  type_classes p
