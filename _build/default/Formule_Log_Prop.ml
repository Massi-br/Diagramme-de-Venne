(** Type des formules de la logique propositionnelle *)
type formule_log_prop =
  | Bot
  | Top
  | Atome of string
  | Et of formule_log_prop * formule_log_prop
  | Ou of formule_log_prop * formule_log_prop
  | Imp of formule_log_prop * formule_log_prop
  | Non of formule_log_prop
  | Xor of formule_log_prop * formule_log_prop
  | Equiv of formule_log_prop * formule_log_prop
  | Aucun of formule_log_prop list
  | Tous of formule_log_prop list
  | AuMoins of int * formule_log_prop list
  | AuPlus of int * formule_log_prop list


(** Évalue une formule en fonction d'une interprétation. *)
  let rec eval (i: string list) : formule_log_prop -> bool = function
  | Bot -> false
  | Top -> true
  | Atome a -> List.mem a i
  | Et (f1, f2) -> eval i f1 && eval i f2
  | Ou (f1, f2) -> eval i f1 || eval i f2
  | Imp (f1, f2) -> not (eval i f1) || eval i f2
  | Non f -> not (eval i f)
  | Xor (f1, f2) -> (eval i f1 && not (eval i f2)) 
                 || (not (eval i f1) && eval i f2)
  | Equiv (f1, f2) -> eval i f1 = eval i f2
  | Aucun lst -> List.for_all (fun f -> not (eval i f)) lst
  | Tous lst -> List.for_all (eval i) lst
  | AuMoins (k, lst) -> List.length (List.filter (eval i) lst) >= k
  | AuPlus (k, lst) -> List.length (List.filter (eval i) lst)  <= k


(** Calcule toutes les interprétations pour une liste d'atomes donnée. *)
let rec all_interpretations : string list -> string list list =  function
    [] -> [[]]
  | x::xs -> let r = all_interpretations xs in
              r @ List.map (fun i -> x :: i) r              

(* extrait la liste des atomes d'une formule *)
let rec extract : formule_log_prop -> string list = function
  | Bot | Top -> []
  | Atome a -> [a]
  | Et (f1, f2) | Ou (f1, f2) | Imp (f1, f2) | Xor (f1, f2) | Equiv (f1, f2) ->
    extract f1 @ extract f2
  | Non f' -> extract f'
  | Aucun lst | Tous lst | AuMoins (_, lst) | AuPlus (_, lst) ->
            List.concat (List.map extract lst)
  ;;


(** table_verite alpha f : renvoie la table de vérité de f sur les atomes issus de f ou de alpha *)
let table_verite (f : string list) (a : formule_log_prop) :
    (string list * bool) list = 
    let fusion lst1 lst2 =
      let rec fusionner acc = function
        | [] -> List.rev acc
        | x :: xs when List.mem x acc -> fusionner acc xs
        | x :: xs -> fusionner (x :: acc) xs
      in
      fusionner [] (lst1 @ lst2)
    in 
    let interpretations = all_interpretations (fusion (extract a) f) in
    List.map (fun interp -> (interp, eval interp a)) (List.rev interpretations)
;;

(** string_of_formule_log_prop_var s f : conversion d'une formule f en chaîne de caractères,
    en les représentant comme des prédicats unaires appliqués sur des 
    occurrences de la variable s. *)
let rec string_of_formule_log_prop_var (s : string) (f : formule_log_prop) : string =
  let wrap str = "(" ^ str ^ ")" in
    match f with
      | Bot -> "⊥"
      | Top -> "T"
      | Atome a -> a ^ wrap s
      | Et (f1, f2) -> wrap (string_of_formule_log_prop_var s f1 ^ " ∧ " ^ string_of_formule_log_prop_var s f2)
      | Ou (f1, f2) -> wrap (string_of_formule_log_prop_var s f1 ^ " v " ^ string_of_formule_log_prop_var s f2)
      | Imp (f1, f2) -> wrap (string_of_formule_log_prop_var s f1 ^ " -> " ^ string_of_formule_log_prop_var s f2)
      | Non f -> wrap ("¬ " ^ string_of_formule_log_prop_var s f)
      | Xor (f1, f2) -> wrap (string_of_formule_log_prop_var s f1 ^ " ⊕ " ^ string_of_formule_log_prop_var s f2)
      | Equiv (f1, f2) -> wrap (string_of_formule_log_prop_var s f1 ^ " ↔ " ^ string_of_formule_log_prop_var s f2)
      | Aucun lst -> "Aucun(" ^ String.concat "; " (List.map (string_of_formule_log_prop_var s) lst) ^ ")"
      | Tous lst -> "Tous(" ^ String.concat ", " (List.map (string_of_formule_log_prop_var s) lst) ^ ")"
      | AuMoins (k, lst) -> "AuMoins(" ^ string_of_int k ^ ", " ^ String.concat "; " (List.map (string_of_formule_log_prop_var s) lst) ^ ")"
      | AuPlus (k, lst) -> "AuPlus(" ^ string_of_int k ^ ", " ^ String.concat "; " (List.map (string_of_formule_log_prop_var s) lst) ^ ")"
    ;;