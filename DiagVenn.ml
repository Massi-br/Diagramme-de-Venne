(* open Formule_Syllogisme
open Formule_Log_Prop *)

(* open Formule_Log_Prop *)

module Predicate_set = Set.Make (String)
(** Module des ensembles de prédicats représentés par des chaines de caractères *)

(** Type des remplissages possibles d'un diagramme de Venn *)
type fill = Vide | NonVide

module Diag = Map.Make (Predicate_set)
(** Module des Maps dont les clés sont des ensembles de chaines de caractères *)

type diagramme = fill Diag.t
(** Type des diagrammes de Venn *)

(** string_of_diag d : conversion d'un diagramme d en une chaine de caractères *)
let string_of_diag (d : diagramme) : string =
  let string_of_fill = function
    | Vide -> "Vide"
    | NonVide -> "Non Vide"
  in
  Diag.fold (fun predicats fill acc ->
    let predicats_str = 
      if Predicate_set.is_empty predicats then
        "∅"
      else
        Predicate_set.fold (fun pred acc ->
              if acc = "" 
              then pred 
              else acc ^ ", " ^ pred) predicats "" in
      let verif = if predicats_str = "∅" then "\t∅ -> " ^ string_of_fill fill ^ "\n" 
                  else 
                    acc ^ "\t{" ^ predicats_str ^ "} -> " ^ string_of_fill fill ^ "\n" in verif
  ) d ""


let diag_from_formule (a : string list) (f : formule_syllogisme) : diagramme list =
    let table = table_verite a (match f with PourTout f' | IlExiste f' -> f') in
      
    match f with
      | PourTout _ ->
        [List.fold_left (fun acc (t, result) ->
          if not result then Diag.add (Predicate_set.of_list t) Vide acc
          else acc
        ) Diag.empty table]
    
      | IlExiste _ ->
        let true_atoms =
          List.fold_left (fun (acc, acc_list) (t, result) ->
            if result then
              let t = Diag.add (Predicate_set.of_list t) NonVide acc in
              (acc, t::acc_list)
            else
              (acc, acc_list)
          ) (Diag.empty, []) table
        in 
        snd true_atoms
        

(** conj_diag d1 d2 : Calcule la combinaison/conjonction de deux diagrammes, 
    renvoyant None si incompatibilité *)
  let conj_diag (d1 : diagramme) (d2 : diagramme) : diagramme option =
    let mergin fill1 fill2 =
      match fill1, fill2 with
      | NonVide, Vide | Vide, NonVide -> None 
      | _ -> Some fill1
    in
    let combine predicates fill1 acc =
      match Diag.find_opt predicates d2 with
      | Some fill2 ->
        (match mergin fill1 fill2 with
          | Some merged_fill -> Some (Diag.add predicates merged_fill acc)
          | None -> None)
      | None -> Some (Diag.add predicates fill1 acc)
    
    in
    let acc_with_d1 = 
      Diag.fold (fun predicates fill acc_opt ->
      match acc_opt with
      | Some acc -> combine predicates fill acc
      | None -> None
    ) d1 (Some Diag.empty) 
  in
  Diag.fold (fun predicates fill acc_opt ->
    match acc_opt with 
    | Some acc -> 
        (match Diag.find_opt predicates acc with
        | Some _ -> acc_opt
        | None -> Some (Diag.add predicates fill acc))
    | None -> acc_opt
  ) d2 acc_with_d1


(** est_compatible_diag_diag dp dc : teste si le diagramme dp d'une prémisse est compatible
    avec le diagramme dc d'une conclusion *)
let est_compatible_diag_diag (dp : diagramme) (dc : diagramme) : bool =
  Diag.for_all (fun predicates fill_dc ->
    match Diag.find_opt predicates dp with
      | Some fill_dp -> fill_dp = fill_dc
      | None -> false
  ) dc
    

(** est_compatible_diag_list dp dcs : teste si un diagramme dp d'une prémisse est compatible
    avec un des diagrammes de la liste dcs,
    diagrammes issus d'une conclusion *)
let est_compatible_diag_list (dp : diagramme) (dcs : diagramme list) : bool =
  List.exists (fun dc -> est_compatible_diag_diag dp dc) dcs
    

(** est_compatible_list_list dps dcs : teste si chacun des diagrammes de dps, diagrammes issus de prémisses,
    est compatible avec au moins un des diagrammes de dcs, diagrammes issus d'une conclusion *)
let est_compatible_list_list (dps : diagramme list) (dcs : diagramme list) : bool =
  List.for_all (fun dp -> est_compatible_diag_list dp dcs) dps


  (* TOOLS *)
  (* ---------------------------------------------------------------------------------- *)
  (* extrait la liste des atomes des formules contenant le quantificateur universel *)
  let use_atomes (ps : formule_syllogisme list) : string list =
    let extract_atoms_from_formula formula =
      match formula with
      | PourTout f1 | IlExiste f1 -> extract f1
    in
  
    let merge_unique_atoms atoms_for_all formula =
      let atoms = extract_atoms_from_formula formula in
      let new_atoms = List.filter 
          (fun atom -> not (List.mem atom atoms_for_all)) atoms 
      in
      atoms_for_all @ new_atoms
    in
    List.fold_left merge_unique_atoms [] ps
  
  (* Définition des formules logiques
let formule1 = PourTout (Et (Atome "p", Atome "q"))
let formule2 = IlExiste (Ou (Atome "r", Atome "s"))
let formule3 = PourTout (Imp (Atome "t", Atome "u"))

(* Liste de formules syllogistiques *)
let liste_formules = [formule1; formule2; formule3]

(* Exécution de la fonction use_atomes *)
let resultats = use_atomes liste_formules *)


  
  (* retourne la liste de diagramme de la combinaison des prémisses  
     (une liste de formules syllogistes) représenter par ps *)
  let combine_diag_premisses (ps : formule_syllogisme list) : diagramme list = 
    let diag_universels =
      List.flatten (List.map (fun f ->
        match f with
        | PourTout _ ->  diag_from_formule [] f
        | _ -> []
      ) ps)
    in
    let diag_existentiels =
      List.flatten (List.map (fun f ->
        match f with
        | IlExiste _ -> diag_from_formule (use_atomes ps)  f
        | _ -> []
      ) ps)
    in
    
    match diag_universels with
    | [] -> []
    | fd :: rd ->
      let combine_diagrams acc diag =
        match conj_diag acc diag with
        | Some d -> d
        | None -> acc
    in

    let combine_diagrams_2 acc diag = 
      match conj_diag acc diag with
      | Some d -> Some d
      | None -> None
    in
    
    let universeles_combine =
      List.fold_left combine_diagrams fd rd
    in

    List.filter_map (combine_diagrams_2 universeles_combine)
    diag_existentiels 

  (* retourne la liste de diagrammes de la formule syllogiste répresenter par c 
     en fonction des atomes de la liste de formules syllogistes représenter par ps *)
  let diag_conclusion (ps : formule_syllogisme list) (c : formule_syllogisme) 
  : diagramme list = 
    diag_from_formule (use_atomes ps) c 


  
  (** diag_incompatible dp dc : renvoie un diagramme de la liste dp qui n'est pas
    compatible avec un diagramme de la liste de diagrammes dc de la conclusion, 
    s'il en existe un. Renvoie None sinon. *)
  let rec diag_incompatible (dp : diagramme list) (dc : diagramme list) 
  : diagramme option =
    match dp with
    | [] -> None
    | d :: _ when not (est_compatible_diag_list d dc) -> Some d
    | _ :: rds -> diag_incompatible rds dc
  (* ---------------------------------------------------------------------------------- *)


(** est_compatible_premisses_conc ps c : teste si une liste de prémisses ps est compatible avec une conclusion c *)
let est_compatible_premisses_conc (ps : formule_syllogisme list) 
(c : formule_syllogisme) : bool = 
  est_compatible_list_list (combine_diag_premisses ps) (diag_conclusion ps c)



(** temoin_incompatibilite_premisses_conc_opt ps c : renvoie un diagramme de la combinaison des 
    prémisses ps incompatible avec la conclusion c s'il existe, None sinon *)
  let temoin_incompatibilite_premisses_conc_opt (ps : formule_syllogisme list)
  (c : formule_syllogisme) : diagramme option =
    if est_compatible_premisses_conc ps c then None
    else
      let dp = combine_diag_premisses ps in
      let dc = diag_conclusion ps c in
      diag_incompatible dp dc


(** temoins_incompatibilite_premisses_conc ps c : renvoie les diagrammes de la combinaison
    des prémisses ps incompatibles avec la conclusion c *)
    let temoins_incompatibilite_premisses_conc (ps : formule_syllogisme list)
    (c : formule_syllogisme) : diagramme list =
    let dp = combine_diag_premisses ps in
    let dc = diag_conclusion ps c in
    let rec all_incompatibilite acc dp = 
      match diag_incompatible dp dc with
      | None -> List.rev acc
      | Some d -> all_incompatibilite (d :: acc) (List.tl dp)
    in 
    all_incompatibilite [] dp