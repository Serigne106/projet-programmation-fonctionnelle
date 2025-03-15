open Syntax 


type valeur = 
  | ValInt of int 
  | ValBool of bool

type var_val = {var:idvar; valeur:valeur}
type env_val = var_val list
type val_fun = ValFunc of idvar list * expr
(*Fonction pour chercher la valeur  d'une variable dans l'environnement *)
let rec chercher_val x env_val =
  match env_val with
  | [] -> failwith ("Variable non définie: " ^ x)  (* La variable n'est pas trouvée *)
  | c :: rest -> if x = c.var then c.valeur else chercher_val x rest  (* Si la variable est trouvée, on retourne son type, sinon on continue la recherche *)

(* Fonction pour chercher une fonction dans l'environnement *)
let rec chercher_fonction id env_funs =

let rec eval_expr env e =
  match e with
  | Var x -> begin let res=chercher_val x env in match res with 
    | ValInt a-> ValInt a
    | ValBool b-> ValBool b
    end
  | Int x-> ValInt x

  | Bool b-> ValBool b
  
  | BinaryOp (op, e1, e2) -> (
      let res1 = eval_expr env e1 in
      let res2 = eval_expr env e2 in
      match (op,res1,res2) with
      | (Plus,ValInt a, ValInt b)  -> ValInt(a + b)   (* Les deux opérandes doivent être des entiers *)
      | (Minus,ValInt a, ValInt b)  -> ValInt(a - b)
      | (Mult,ValInt a, ValInt b)  -> ValInt(a * b) 
      | (Div,ValInt a, ValInt b)  -> ValInt(a / b)

      | (And,ValBool a, ValBool b)  -> ValBool(a && b)   (* Les deux opérandes doivent être des booléens *)
      | (Or,ValBool a, ValBool b)  -> ValBool(a || b)  

      | (Equal,ValInt a, ValInt b)  -> ValBool(a == b)
      | (NEqual,ValInt a, ValInt b)  -> ValBool(a <> b)
      | (Less,ValInt a, ValInt b)  -> ValBool(a < b) 
      | (LessEq,ValInt a, ValInt b)  -> ValBool(a <=b)
      | (Great,ValInt a, ValInt b)  -> ValBool(a > b) 
      | (GreatEq,ValInt a, ValInt b)  -> ValBool(a >=b)

      |(Plus,ValBool _, ValBool _) -> failwith "l'operateur plus n'est pas defini pour les booléens";
      |(Minus,ValBool _, ValBool _) -> failwith "l'operateur minus n'est pas defini pour les booléens";
      |(Div,ValBool _, ValBool _) -> failwith "l'operateur div n'est pas defini pour les booléens";
      |(Mult,ValBool _, ValBool _) -> failwith "l'operateur mult n'est pas defini pour les booléens";

      |(Equal,ValBool _, ValBool _) -> failwith "l'operateur = n'est pas defini pour les booléens";
      |(NEqual,ValBool _, ValBool _) -> failwith "l'operateur <> egal n'est pas defini pour les booléens";
      |(Less,ValBool _, ValBool _) -> failwith "l'operateur < n'est pas defini pour les booléens";
      |(LessEq,ValBool _, ValBool _) -> failwith "l'operateur <= n'est pas defini pour les booléens";
      |(Great,ValBool _, ValBool _) -> failwith "l'operateur > n'est pas defini pour les booléens";
      |(GreatEq,ValBool _, ValBool _) -> failwith "l'operateur >= n'est pas defini pour les booléens";

      |(And,ValInt _, ValInt _) -> failwith "l'operateur and n'est pas defini pour les entiers";
      |(Or,ValInt _, ValInt _) -> failwith "l'operateur or n'est pas defini pour les entiers";

      |(_,ValBool _, ValInt _) -> failwith "les deux opérandes doivent être de meme type";
      |(_,ValInt _, ValBool _) -> failwith "les deux opérandes doivent être de meme type";
    )

    | UnaryOp (Not, e) -> 
      let res = eval_expr env e in
      (match res with
       | ValBool true  -> ValBool false
       | ValBool false -> ValBool true
       | _ -> failwith "L'opérateur 'not' prend un booléen")

    | If (cond, e1, e2) -> 
    let res_cond = eval_expr env cond in
    (match res_cond with
     | ValBool true  -> eval_expr env e1  (* Si la condition est vraie, on évalue e1 *)
     | ValBool false -> eval_expr env e2  (* Sinon, on évalue e2 *)
     | _ -> failwith "La condition d'un if doit être un booléen")

    | Let (x, _, e1, e2) ->
        let valeur_e1 = eval_expr env e1 in  (* On évalue e1 *)
        let nouvel_env = { var = x; valeur = valeur_e1 } :: env in
        eval_expr nouvel_env e2  (* On évalue e2 dans ce nouvel environnement *)

   | App (f, args) -> 
      (* 1. Chercher la fonction dans l'environnement *)
      let f_val = chercher_fonction f env in
      match f_val with
      | ValFunc (param_names, body) -> 
          (* 2. Évaluer les arguments *)
          let args_values = List.map (fun arg -> eval_expr env arg) args in
          
          (* 3. Associer les arguments aux paramètres de la fonction *)
          let new_env = List.fold_left2
              (fun acc param_name arg_val -> 
                 (* Créer une nouvelle variable associée à la valeur *)
                 { var = param_name; valeur = arg_val } :: acc)
              env (* On commence avec l'environnement actuel *)
              param_names (* Les noms des paramètres de la fonction *)
              args_values (* Les valeurs des arguments évaluées *)
          in
          
          (* 4. Évaluer le corps de la fonction avec le nouvel environnement *)
          eval_expr new_env body
      | _ -> failwith "L'identifiant n'est pas une fonction"
      (* Autres cas de `eval_expr` *)
      | _ -> failwith "Erreur d'évaluation"





  let rec eval_prog prog =
         (* 2. Construire l'environnement des fonctions *)
  let build_env_fonctions prog =
    List.fold_left (fun env f_decl ->
      let { id; var_list; typ_retour; corps } = f_decl in
      let param_names = List.map fst var_list in
      let new_func = ValFunc (param_names, corps, env) in
      { var = id; valeur = new_func } :: env
    ) [] prog
  in

  (* 3. Evaluation du programme *)
  let env_fonctions = build_env_fonctions prog in

  (* Si le programme a une expression principale, on l'évalue aussi *)
  (* Ici, on suppose que le programme a une expression principale à évaluer,
     donc on évalue l'expression principale avec l'environnement des fonctions. *)
  eval_expr env_fonctions (Var "main")