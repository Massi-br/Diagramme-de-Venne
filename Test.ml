(* open Formule_Syllogisme
open Formule_Log_Prop
open DiagVenn *)

let a = Atome "a"
let b = Atome "b"
let c = Atome "c"
let d = Atome "d"
let p1 = PourTout (Imp (Ou (a, b), c))
let p2 = PourTout (Imp (c, Ou (a, b)))
let p2'= PourTout (Imp (c, Et (a,b)))
let p3 = IlExiste a
let p4 = IlExiste (Imp (a, Non b))
let p5 = PourTout (Imp (Xor (a, b), c))
let p6 = PourTout (Imp (Non c, a))
let c1 = IlExiste b
let c2 = IlExiste c
let c3 = IlExiste d

(** test premisses conclusion : teste si chacun des diagrammes de la combinaison
    de la liste prémisses est compatible avec au moins un des diagrammes de conclusion,
    tout en traçant les calculs réalisés et les diagrammes calculés,
    et en affichant tous les contre-exemples le cas échéant. *)
let test (premisses : formule_syllogisme list) (conclusion : formule_syllogisme) : unit =
  (* Affiche une liste de diagrammes *)
  let print_diagram_list diagrams =
    List.iteri (fun i d ->
      Printf.printf "    Diagramme %d :\n%s\n" (i + 1) (string_of_diag d)
    ) diagrams
  in
    
  (* Affiche les résultats pour chaque prémisse et la conclusion *)
  let print_results premisses conclusion diag_premisses diag_combinaison diag_conclusion =
    Printf.printf "Prémisses :\n";
    List.iter (fun f -> Printf.printf "%s\n" (string_of_formule f);) premisses;
    Printf.printf "Conclusion :\n";
    Printf.printf "%s\n" (string_of_formule conclusion);      
    Printf.printf "\nDiagrammes de chaque prémisse :\n";
    List.iteri (fun i f ->
      Printf.printf "  Diagrammes de la prémisse %d\n" (i + 1);
      print_diagram_list f
    ) diag_premisses;
    
    Printf.printf "Diagrammes de la combinaison :\n";
    print_diagram_list diag_combinaison;
        
    Printf.printf "Diagrammes de la conclusion :\n";
    print_diagram_list diag_conclusion;
    
    if est_compatible_list_list diag_combinaison diag_conclusion then
      Printf.printf "Conclusion compatible avec les diagrammes.\n"
    else
      Printf.printf "Conclusion incompatible avec les diagrammes, contre-exemples :\n";
      print_diagram_list (temoins_incompatibilite_premisses_conc premisses conclusion)
  in
    
  let diag_premisses = 
    List.map (fun f ->
      match f with
      | PourTout _ | IlExiste _ ->  diag_from_formule [] f) premisses
    in
    let diag_combinaison = combine_diag_premisses premisses in
    let diag_conclusion = diag_conclusion premisses conclusion 
    in
    
  print_results premisses conclusion diag_premisses diag_combinaison diag_conclusion