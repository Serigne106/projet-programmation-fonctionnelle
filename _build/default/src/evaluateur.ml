open Syntax

(* Définition des types de valeurs possibles *)
type valeur = 
  | ValInt of int  (* Représente une valeur entière *)
  | ValBool of bool  (* Représente une valeur booléenne *)
  | ValFloat of float  (* Représente une valeur flottante *)
  | ValUnit  (* Représente la valeur unité *)
  
(* Définition des environnements d'évaluation *)
type env_val = (idvar * valeur) list  (* Associe les variables à leurs valeurs *)
type env_funs = (idfun * (idvar list * expr)) list  (* Associe les fonctions à leurs paramètres et leur corps *)

(* Fonction pour chercher une variable dans l'environnement des valeurs *)
let rec chercher_val x env_vals =
  match env_vals with
  | [] -> failwith ("Variable non définie: " ^ x)  (* Si la variable n'est pas trouvée, on lève une exception *)
  | (y, v) :: rest -> if x = y then v else chercher_val x rest  (* Si la variable est trouvée, on retourne sa valeur, sinon on continue la recherche *)

(* Fonction pour chercher une fonction dans l'environnement des fonctions *)
let rec chercher_fonction id env_funs =
  match env_funs with
  | [] -> failwith ("Fonction non définie: " ^ id)  (* Si la fonction n'est pas trouvée, on lève une exception *)
  | (g, (params, body)) :: rest -> 
      if id = g then (params, body)  (* Si la fonction est trouvée, on retourne ses paramètres et son corps *)
      else chercher_fonction id rest  (* Sinon, on continue la recherche *)
  
(* Évaluation des expressions *)
let rec eval_expr env_val env_funs e =
  match e with
  | Var x -> chercher_val x env_val  (* Si l'expression est une variable, on cherche sa valeur dans l'environnement *)
  | Int x -> ValInt x  (* Si l'expression est un entier, on retourne sa valeur *)
  | Bool b -> ValBool b  (* Si l'expression est un booléen, on retourne sa valeur *)
  | Float f -> ValFloat f  (* Si l'expression est un flottant, on retourne sa valeur *)
  | Unit -> ValUnit

  (* Évaluation des opérations binaires *)
  | BinaryOp (op, e1, e2) -> (
      let v1 = eval_expr env_val env_funs e1 in  (* Évaluer le premier opérande *)
      let v2 = eval_expr env_val env_funs e2 in  (* Évaluer le second opérande *)
      match (op, v1, v2) with
      | (Plus, ValInt a, ValInt b) -> ValInt (a + b)  (* Addition *)
      | (Minus, ValInt a, ValInt b) -> ValInt (a - b)  (* Soustraction *)
      | (Mult, ValInt a, ValInt b) -> ValInt (a * b)  (* Multiplication *)
      | (Div, ValInt a, ValInt b) -> 
          if b = 0 then failwith "Division par zéro"  (* Gestion de la division par zéro *)
          else ValInt (a / b)

      | (And, ValBool a, ValBool b) -> ValBool (a && b)  (* ET logique *)
      | (Or, ValBool a, ValBool b) -> ValBool (a || b)  (* OU logique *)

      | (Equal, ValInt a, ValInt b) -> ValBool (a = b)  (* Égalité pour les entiers *)
      | (NEqual, ValInt a, ValInt b) -> ValBool (a <> b)  (* Inégalité pour les entiers *)
      | (Less, ValInt a, ValInt b) -> ValBool (a < b)  (* Inférieur à *)
      | (LessEq, ValInt a, ValInt b) -> ValBool (a <= b)  (* Inférieur ou égal à *)
      | (Great, ValInt a, ValInt b) -> ValBool (a > b)  (* Supérieur à *)
      | (GreatEq, ValInt a, ValInt b) -> ValBool (a >= b)  (* Supérieur ou égal à *)
      
      | (Equal, ValFloat a, ValFloat b) -> ValBool (a = b)  (* Égalité pour les flotants *)
      | (NEqual, ValFloat a, ValFloat b) -> ValBool (a <> b)  (* Inégalité pour les flotants *)
      | (Less, ValFloat a, ValFloat b) -> ValBool (a < b)  (* Inférieur à *)
      | (LessEq, ValFloat a, ValFloat b) -> ValBool (a <= b)  (* Inférieur ou égal à *)
      | (Great, ValFloat a, ValFloat b) -> ValBool (a > b)  (* Supérieur à *)
      | (GreatEq, ValFloat a, ValFloat b) -> ValBool (a >= b)  (* Supérieur ou égal à *)

      |(PlusPT, ValFloat a, ValFloat b) -> ValFloat (a+.b)  (* Addition *)
      |(MinusPT, ValFloat a, ValFloat b) -> ValFloat (a-.b)  (* Addition *)
      |(MultPT, ValFloat a, ValFloat b) -> ValFloat (a*.b)  (* Addition *)
      |(DivPT, ValFloat a, ValFloat b) -> ValFloat (a/.b)  (* Addition *)

      | _ -> failwith "Erreur de types dans l'opération binaire"  (* Si les types ne correspondent pas *)
    )

  (* Évaluation des opérations unaires *)
  | UnaryOp (Not, e) -> (
      match eval_expr env_val env_funs e with
      | ValBool b -> ValBool (not b)  (* Négation logique *)
      | _ -> failwith "L'opérateur 'not' prend un booléen"  (* Si le type n'est pas un booléen *)
    )

  (* Évaluation des expressions conditionnelles *)
  | If (cond, e1, e2) -> (
      match eval_expr env_val env_funs cond with
      | ValBool true -> eval_expr env_val env_funs e1  (* Si la condition est vraie, on évalue e1 *)
      | ValBool false -> eval_expr env_val env_funs e2  (* Sinon, on évalue e2 *)
      | _ -> failwith "La condition du 'if' doit être un booléen"  (* Si la condition n'est pas un booléen *)
    )

  (* Évaluation des expressions `let` *)
  | Let (x, _, e1, e2) ->
      let valeur_e1 = eval_expr env_val env_funs e1 in  (* Évaluer e1 *)
      let nouvel_env = (x, valeur_e1) :: env_val in  (* Ajouter la variable à l'environnement *)
      eval_expr nouvel_env env_funs e2  (* Évaluer e2 dans le nouvel environnement *)

  | LetRec (f, params, _, _, body) ->
        let env_val' = (f, ValUnit) :: env_val in  (* Add function to the value environment *)
        let env_funs' = (f, (List.map fst params, body)) :: env_funs in  (* Add function to the function environment *)
        eval_expr env_val' env_funs' body  (* Evaluate the function body *)
    

  (* Évaluation des appels de fonctions *)
  | App (f, args) ->
    let (param_names, body) = chercher_fonction f env_funs in
    let args_values = List.map (fun arg -> eval_expr env_val env_funs arg) args in
    if List.length param_names <> List.length args_values then
      failwith ("Mauvais nombre d'arguments pour la fonction " ^ f);
    (* Associer les paramètres aux valeurs tout en conservant l’environnement existant *)
    let new_env_val = List.fold_left2 (fun acc param value -> (param, value) :: acc) env_val param_names args_values in
    eval_expr new_env_val env_funs body

  | PrintInt  e -> 
    begin match eval_expr env_val env_funs e with
    | ValInt n -> print_endline (string_of_int n);
                 ValUnit
    | _ -> failwith "Expression non reconnue" 
   end
  | _ -> failwith "Expression non reconnue"



(* Évaluation d'un programme *)
let eval_prog prog =
  (* Construire l’environnement des fonctions *)
  let build_env_fonctions prog =
    List.fold_left (fun env_funs f_decl ->
      let { id; var_list; corps; _ } = f_decl in
      let param_names = List.map fst var_list in  (* Extraire les noms des paramètres *)
      (id, (param_names, corps)) :: env_funs  (* Ajouter la fonction à l'environnement *)
    ) [] prog
  in

  let env_funs = build_env_fonctions prog in  (* Construire l'environnement des fonctions *)

  try
    let (params, body) = chercher_fonction "main" env_funs in  (* Chercher la fonction `main` *)
    if params <> [] then failwith "La fonction 'main' doit être sans paramètres";  (* Vérifier que `main` n'a pas de paramètres *)
    (* Évaluer le corps de `main` et afficher le résultat *)
    let result = eval_expr [] env_funs body in
    match result with
    | ValInt n -> print_endline (string_of_int n)  (* Afficher un entier *)
    | ValBool b -> print_endline (string_of_bool b)  (* Afficher un booléen *)
    | ValFloat f -> print_endline (string_of_float f)  (* Afficher un flottant *)
    | ValUnit -> print_endline "()"  (* Afficher la valeur unité *)
  with Not_found ->
    failwith "La fonction 'main' est absente du programme"  (* Si `main` n'est pas définie *)