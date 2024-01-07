(* open Formule_Log_Prop *)

(** Type des formules utilisées pour les syllogismes *)
type formule_syllogisme =
  | PourTout of formule_log_prop
  | IlExiste of formule_log_prop

(** string_of_formule f : conversion d'une formule f en chaîne de caractères,
    en considérant des prédicats unaires appliqués sur des 
    occurrences de la variable s. (remarque : si vous avez un probleme de visualisation de \t utiliser
     la fonction prédefini print_endline)*)
    let string_of_formule: formule_syllogisme -> string = function
    | PourTout f -> "\t∀x " ^ string_of_formule_log_prop_var "x" f 
    | IlExiste f -> "\t∃x " ^ string_of_formule_log_prop_var "x" f
  ;;
