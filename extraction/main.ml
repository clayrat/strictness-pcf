(* Driver for the extracted PCF type checker, evaluator, and analyser.

   Runs the *extracted* [infer]/[check], [evalFuel], and [analyse] (checker.ml,
   generated from Extract.v) on representative cases and prints what the
   algorithms answer — including errors, stuck reports, and finite abstract
   function tables.

   Nothing here is verified; it is a printer plus a table of calls. Everything
   it prints is also frozen as a kernel-checked [reflexivity] in
   theories/Tests.v, so the two agree by construction. *)

open Checker

(* ------------------------------------------------------------------ *)
(* Printing                                                            *)

let rec pp_ty = function
  | Tnat -> "ℕ"
  | Tarr (a, b) -> pp_ty_atom a ^ " → " ^ pp_ty b

and pp_ty_atom = function
  | Tnat -> "ℕ"
  | Tarr _ as a -> "(" ^ pp_ty a ^ ")"

let rec pp = function
  | Tvar x -> x
  | Tlam (x, u) -> "λ" ^ x ^ ". " ^ pp u
  | Tapp (f, u) -> pp_fun f ^ " " ^ pp_atom u
  | Tnum n -> string_of_int n
  | Tsucc u -> "succ " ^ pp_atom u
  | Tpred u -> "pred " ^ pp_atom u
  | Tifz (c, a, b) -> "ifz " ^ pp c ^ " then " ^ pp a ^ " else " ^ pp b
  | Tfix (a, u) -> "fix_" ^ pp_ty_atom a ^ " " ^ pp_atom u
  | Tann (u, a) -> "(" ^ pp u ^ " : " ^ pp_ty a ^ ")"

(* the head of an application may itself be an application, but not a λ *)
and pp_fun = function
  | Tapp _ as t -> pp t
  | t -> pp_atom t

and pp_atom = function
  | (Tvar _ | Tnum _ | Tann _) as t -> pp t
  | t -> "(" ^ pp t ^ ")"

(* The example programs are big; in an error message the *name* is what the
   reader needs, so print it when the offending subterm is one of them. *)
let named =
  [ (add, "add"); (mul, "mul"); (fact, "fact"); (omega, "Ω");
    (delta, "δ"); (loop, "loop"); (slow, "slow");
    (strict_succ, "λx. succ x"); (const_zero, "λx. 0") ]

let describe t =
  match List.find_opt (fun (u, _) -> u = t) named with
  | Some (_, n) -> n
  | None -> pp t

let pp_error = function
  | E_Unbound x -> Printf.sprintf "unbound variable %s" x
  | E_NoSynth t ->
    Printf.sprintf "cannot synthesize a type for %s" (describe t)
  | E_NotFun (t, a) ->
    Printf.sprintf "%s has type %s, so it cannot be applied" (describe t) (pp_ty a)
  | E_LamNotFun (t, a) ->
    Printf.sprintf "%s is a function, but %s was expected" (describe t) (pp_ty a)
  | E_Mismatch (t, expected, got) ->
    Printf.sprintf "%s: expected %s, got %s" (describe t) (pp_ty expected) (pp_ty got)

let pp_infer t =
  match infer [] t with
  | Ok a -> "⇑ " ^ pp_ty a
  | Err e -> "error: " ^ pp_error e

let pp_check t a =
  match check [] t a with
  | Ok () -> "⇓ ok"
  | Err e -> "error: " ^ pp_error e

(* ------------------------------------------------------------------ *)
(* Checker examples                                                    *)

(* Padding by code points, not bytes: every label below is full of ℕ, λ and Ω. *)
let utf8_width s =
  let n = ref 0 in
  String.iter (fun c -> if Char.code c land 0xC0 <> 0x80 then incr n) s;
  !n

let pad w s = s ^ String.make (max 1 (w - utf8_width s)) ' '

let section title =
  Printf.printf "\n%s\n%s\n" title (String.make (utf8_width title) '-')

let row label answer note =
  Printf.printf "  %s%s%s\n" (pad 36 label) (pad 50 answer) note

let infer_row name t note = row ("infer  " ^ name) (pp_infer t) note
let check_row name t a note =
  row (Printf.sprintf "check  %s : %s" name (pp_ty a)) (pp_check t a) note

let nn = Tarr (Tnat, Tnat)

let () =
  print_endline
    "PCF: bidirectional checker, CBN evaluator, and strictness analyser (extracted from Rocq).";

  section "Representative PCF programs";
  check_row "fact" fact nn "the recursive factorial";
  infer_row "fact" fact "fix is annotated, so it also synthesizes";
  check_row "add" add (Tarr (Tnat, nn)) "";
  check_row "loop" loop nn "certified strict, yet loop 0 diverges";
  check_row "slow" slow nn "slow but total";

  section "The two Ωs: divergence accepted, self-application rejected";
  infer_row "Ω = fix_ℕ (λx. x)" omega "accepting this is correct — operationally it diverges";
  infer_row "(λx. x x) (λx. x x)" omega_untyped "no type at all: not a missing annotation";
  check_row "δ = λx. x x" delta nn "an expected type does not help either";

  section "λ in a synthesizing position: the error an annotation repairs";
  infer_row "λx. x" ex_id "unsynthesizable, not ill-typed";
  check_row "λx. x" ex_id nn "with an expected type it checks";
  infer_row "(λx. x : ℕ → ℕ)" ex_id_ann "the annotation is the repair";
  infer_row "(λx. 0) Ω" cbn_flagship "the central CBN example needs one too";
  infer_row "((λx. 0) : ℕ → ℕ) Ω" cbn_flagship_ann "typed ℕ, and still contains Ω";

  section "Where the algorithm localizes an error";
  infer_row "(λf. f 0 : (ℕ → ℕ) → ℕ) 3" ex_apply_to_three
    "the argument is blamed, not the application";
  infer_row "fact fact" (Tapp (fact, fact)) "the argument again";
  infer_row "succ (λx. x)" stuck_succ "a stuck term, caught statically";
  infer_row "y" (Tvar "y") "lookup by name";

  (* The extracted API is an ordinary OCaml variant type: terms can be built
     here, not only imported from Coq. *)
  section "A term built on the OCaml side";
  let double = Tann (Tlam ("n", Tsucc (Tsucc (Tvar "n"))), nn) in
  infer_row "(λn. succ (succ n) : ℕ → ℕ)" double "";
  infer_row "(λn. succ (succ n) : ℕ → ℕ) 3" (Tapp (double, Tnum 3)) "";
  infer_row "(λn. succ (succ n) : ℕ → ℕ) fact" (Tapp (double, fact)) "";

  (* ---------------- The evaluator ----------------------- *)

  let pp_eval = function
    | Value v -> "Value " ^ pp_atom v
    | Timeout -> "Timeout"
    | Stuck s -> "Stuck at " ^ describe s
  in
  let eval_row fuel name t note =
    row (Printf.sprintf "eval %-4d %s" fuel name) (pp_eval (evalFuel fuel t)) note
  in

  section "Evaluation: call-by-name, with fuel";
  eval_row 5000 "(fact 3)" (Tapp (fact, Tnum 3)) "a value confirms termination";
  eval_row 5000 "Ω" omega "a timeout confirms nothing";
  eval_row 2 "((λx. 0) Ω)" cbn_flagship "the flagship: fuel TWO — Ω never touched";
  eval_row 10 "(succ (λx. x))" stuck_succ "unchecked and stuck; a checked program cannot do this";
  eval_row 100 "((λx. x x) (λx. x x))" omega_untyped "untypable, yet not stuck: it spins";

  section "The key pair: slow vs Ω, same fuel";
  eval_row 10 "(slow 5)" (Tapp (slow, Tnum 5)) "indistinguishable from Ω at this fuel...";
  eval_row 10 "Ω" omega "...literally the same observation";
  eval_row 50 "(slow 5)" (Tapp (slow, Tnum 5)) "more fuel separates them — one way only";

  (* ---------------- The strictness analysis ----------------------- *)

  let rec pp_aval = function
    | AN false -> "\xe2\x8a\xa5"                    (* ⊥ *)
    | AN true -> "\xe2\x8a\xa4"                     (* ⊤ *)
    | AF tbl ->
      "{" ^ String.concat ", "
              (List.map (fun (a, b) -> pp_aval a ^ "\xe2\x86\xa6" ^ pp_aval b) tbl)
      ^ "}"
  in
  let nnn = Tarr (Tnat, nn) in
  let an_row name t ty note = row ("analyse  " ^ name) (pp_aval (analyse t ty)) note in

  section "Strictness analysis: static, and always terminating";
  an_row "λx. succ x" strict_succ nn "⊥↦⊥ certifies strictness";
  an_row "λx. 0" const_zero nn "⊤ means unknown — never \"non-strict\"";
  an_row "Ω" omega Tnat "the analysis computes ⟦Ω⟧♯ = ⊥ — and terminates";
  an_row "fact" fact nn "strict, in dsize(ℕ→ℕ) = 4 abstract iterations";
  an_row "mul" mul nnn "strict in m only — and truly: mul 0 Ω = 0";

  section "The abstract fixpoint iteration, on add";
  let addF = aeval [] [] add_body (Tarr (nnn, nnn)) in
  let it k = pp_aval (afix_approx nnn addF k) in
  row "a0 = \xe2\x8a\xa5" (it 0) "nothing defined yet";
  row "a1 = F#(a0)" (it 1) "already strict in both arguments";
  row "a2 = F#(a1)" (it 2) "= a1: stabilized — the analysis' answer";

  section "Conservativity: success and blindness, one term apart";
  an_row "loop" loop nn "certified strict — and truly: loop Ω diverges";
  an_row "λx. loop 0" blind nn "unknown — yet provably strict: the abstraction forgot 0";

  (* Fail the build if the extracted algorithms ever stop agreeing with
     theories/Tests.v. *)
  assert (infer [] fact = Ok nn);
  assert (infer [] omega = Ok Tnat);
  assert (check [] omega_untyped Tnat <> Ok ());
  assert (infer [] ex_id_ann = Ok nn);
  assert (evalFuel 5000 (Tapp (fact, Tnum 3)) = Value (Tnum 6));
  assert (evalFuel 5000 omega = Timeout);
  assert (evalFuel 2 cbn_flagship = Value (Tnum 0));
  assert (evalFuel 10 stuck_succ = Stuck stuck_succ);
  assert (certified_strict strict_succ = true);
  assert (certified_strict const_zero = false);
  assert (certified_strict fact = true);
  assert (certified_strict slow = true);
  assert (certified_strict loop = true);
  assert (certified_strict blind = false);
  assert (certified_strict omega = false);
  assert (analyse omega Tnat = AN false);
  print_newline ()
