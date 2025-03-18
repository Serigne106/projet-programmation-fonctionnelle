open Syntax 

(* Définition des environnements *)
type env_type = {
  var_env : (idvar * typ) list;  (* Environnement des variables : liste d'associations (nom de variable, type) *)
  fun_env : (idfun * ((idvar * typ) list * typ)) list;  (* Environnement des fonctions : liste d'associations (nom de fonction, (liste de paramètres, type de retour)) *)
}


(* Fonction pour comparer deux listes de types *)
let rec comparer_type env1 env2 = match (env1, env2) with
| ([], []) -> true  (* Les deux listes sont vides, elles sont donc égales *)
| ((idvar1, typ1) :: t1, (idvar2, typ2) :: t2) -> 
    if idvar1 = idvar2 && typ1 = typ2 then comparer_type t1 t2  (* Les têtes des listes sont égales, on compare les queues *)
    else false  (* Les têtes des listes sont différentes, les listes ne sont pas égales *)
| _ -> false  (* Les listes ont des longueurs différentes, elles ne sont pas égales *)

(* Fonction pour chercher une variable dans l'environnement *)
let rec chercher_var x env_vars =
  match env_vars with
  | [] -> failwith ("Variable non définie: " ^ x)  (* La variable n'est pas trouvée *)
  | (y, typ) :: rest -> if x = y then typ else chercher_var x rest  (* Si la variable est trouvée, on retourne son type, sinon on continue la recherche *)

(* Fonction pour chercher une fonction dans l'environnement *)
let rec chercher_fonction id env_funs =
  match env_funs with
  | [] -> failwith ("Fonction non définie: " ^ id)  (* La fonction n'est pas trouvée *)
  | (g, (params, ret_type)) :: rest -> 
      if id = g then (params, ret_type) else chercher_fonction id rest  (* Si la fonction est trouvée, on retourne ses paramètres et son type de retour, sinon on continue la recherche *)

(* Vérification du typage des expressions *)
let rec verif_expr env e typ_attendu =
  match e with
  | Var x -> 
      let t = chercher_var x env.var_env in  (* On cherche le type de la variable *)
      if t = typ_attendu then true  (* Si le type correspond au type attendu, on retourne true *)
      else failwith ("La variable " ^ x ^ " n'a pas le type attendu")

  | Int _ -> typ_attendu = TInt  (* Si l'expression est un entier, le type attendu doit être TInt *)

  | Bool _ -> typ_attendu = TBool  (* Si l'expression est un booléen, le type attendu doit être TBool *)

  | BinaryOp (op, e1, e2) -> (
      match op with
      | Plus | Minus | Mult | Div -> 
          if typ_attendu <> TInt then failwith "Une opération arithmétique doit retourner un entier"; 
          verif_expr env e1 TInt && verif_expr env e2 TInt  (* Les deux opérandes doivent être des entiers *)

      | And | Or -> 
          if typ_attendu <> TBool then failwith "Une opération logique doit retourner un booléen";
          verif_expr env e1 TBool && verif_expr env e2 TBool  (* Les deux opérandes doivent être des booléens *)

      | Equal | NEqual -> 
         let t1 = if verif_expr env e1 TInt then TInt 
           else if verif_expr env e1 TBool then TBool 
            else failwith "Type non supporté pour l'égalité"
          in
         let t2 = if verif_expr env e2 TInt then TInt 
           else if verif_expr env e2 TBool then TBool 
           else failwith "Type non supporté pour l'égalité"
         in
        (*
          let t1 = match e1 with 
            | Var x -> chercher_var x env.var_env 
            | _ -> failwith "Expression incorrecte, une variable est attendue"
          in
          let t2 = match e2 with 
            | Var x -> chercher_var x env.var_env 
            | _ -> failwith "Expression incorrecte, une variable est attendue"
          in
          *)
          if t1 = t2 then typ_attendu = TBool  (* Les deux opérandes doivent être du même type et le type attendu doit être TBool *)
          else failwith "Les deux opérandes d'une comparaison doivent être du même type"
          

  
      | Less | LessEq | Great | GreatEq -> 
          if typ_attendu <> TBool then failwith "Une comparaison doit retourner un booléen";
          verif_expr env e1 TInt && verif_expr env e2 TInt  (* Les deux opérandes doivent être des entiers *)
    )

  | UnaryOp (Not, e) -> 
      if typ_attendu <> TBool then failwith "L'opérateur 'not' doit retourner un booléen";
      verif_expr env e TBool  (* L'opérande doit être un booléen *)

  | If (cond, e1, e2) -> 
      if not (verif_expr env cond TBool) then
        failwith "La condition d'un 'if' doit être un booléen";
      verif_expr env e1 typ_attendu && verif_expr env e2 typ_attendu  (* Les deux branches doivent avoir le type attendu *)

  | Let (x, typ_x, e1, e2) ->
      if not (verif_expr env e1 typ_x) then
        failwith ("Mauvais typage dans 'let' pour la variable " ^ x);
      let new_env = { env with var_env = (x, typ_x) :: env.var_env } in  (* On ajoute la nouvelle variable à l'environnement *)
      verif_expr new_env e2 typ_attendu  (* On vérifie le typage de l'expression e2 dans le nouvel environnement *)

  | App (f, args) ->
      let (params_types, ret_type) = chercher_fonction f env.fun_env in  (* On cherche les paramètres et le type de retour de la fonction *)
      if List.length args <> List.length params_types then
        failwith ("Mauvais nombre d'arguments pour la fonction " ^ f);
      List.iter2
        (fun expr typ_attendu ->
          if not (verif_expr env expr typ_attendu) then
            failwith ("Mauvais type d'argument pour la fonction " ^ f))
        args (List.map snd params_types);  (* On vérifie le typage de chaque argument *)
      ret_type = typ_attendu  (* Le type de retour doit correspondre au type attendu *)

  | _ -> failwith "Erreur de typage"

(* Vérification du typage d'une déclaration de fonction *)
let verif_decl_fun env fdecl =
  let params_env = {
    var_env = List.map (fun (x, t) -> (x, t)) fdecl.var_list; (* Ajout des paramètres à l'env local *)
    fun_env = env.fun_env
  } in
  verif_expr params_env fdecl.corps fdecl.typ_retour (* Vérifie que le corps de la fonction est bien typé *)

(* Vérification d'un programme *)
let verif_prog prog =
  (* Construire un environnement initial avec toutes les fonctions *)
  let init_env = {
    var_env = []; (* Pas de variables globales *)
    fun_env = List.map (fun f -> 
      (f.id, (f.var_list, f.typ_retour)) (* Stocke les paramètres et le type de retour *)
    ) prog
  } in 
  (* Vérifier que toutes les fonctions sont bien typées *)
  let tout_funs_ok = List.for_all (fun f -> verif_decl_fun init_env f) prog in

  (* Vérifier la présence d'une fonction `main` sans paramètres *)
  (*fonction anonyne qui *)
  let est_valid_main = List.exists (fun f -> f.id = "main" && f.var_list = []) prog in
  tout_funs_ok && est_valid_main (* Retourne vrai si tout est bien typé et que main() est défini *)

  


