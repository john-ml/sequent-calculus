type ('a, 'e) result = Ok of 'a | Err of 'e

let (let*) x k = match x with Ok y -> k y | Err e -> Err e

let ( *> ) m1 m2 = let* _ = m1 in m2

(* Types

τ ∷= 0 | 1
   | σ + τ
   | σ × τ
   | σ → τ
   | ¬ τ

*)
type ty
  = Void | Unit
  | Sum of ty * ty
  | Prod of ty * ty
  | Arr of ty * ty
  | Neg of ty
  | Vdash of ty list * ty list

(* Typing contexts: Γ, Δ ∷= · | Γ, x : τ *)

type var = Var of int
type covar = Covar of int

type 'a ctx = 'a -> (ty, [`NotFound]) result
let empty : 'a ctx = fun _ -> Err `NotFound
let add (x : 'a) (t : ty) (c : 'a ctx) : 'a ctx =
  fun x' -> if x = x' then Ok t else c x'

(* Terms *)

type exp
  (* Variables
     | [k]x
     | let x : τ = κ k. e₁ in e₂ *)
  = Axiom of covar * var
  | Let of var * ty * covar * exp * exp
  (* Unit and zero
     | absurd x
     | [k]★ *)
  | Absurd of var
  | Trivial of covar
  (* Products
     | pair k (κ h. e₁) (κ j. e₂)
     | let (y, z) = x in e *)
  | Pair of covar * covar * exp * covar * exp
  | Unpair of var * var * var * exp
  (* Sums
     | let [h, j] = k in e
     | case x (λ y. e₁) (λ z. e₂) *)
  | Uncase of covar * covar * covar * exp
  | Case of var * var * exp * var * exp
  (* Functions
     | [k](λ x. κ j. e)
     | let y = x (κ k. e₁) in e₂ *)
  | Fun of covar * var * covar * exp
  | LetApp of var * var * covar * exp * exp
  (* Negation
     | let x -> k in e
     | let x <- k in e *)
  | ToCo of var * covar * exp
  | OfCo of var * covar * exp
  (* Sequents
     | [k](λ x .. . κ j .. . e)
     | case x (κ k. e₁) .. of (λ y. e₂) .. end *)
  (* | LK of covar * int * (covar list -> exp) * int * (var list -> exp) *)

(* Typing *)

let find_var x vars =
  match vars x with
  | Err `NotFound -> Err (`NoVar x)
  | Ok t -> Ok t

let find_covar k covars =
  match covars k with
  | Err `NotFound -> Err (`NoCovar k)
  | Ok t -> Ok t

let as_unit m =
  let* ty = m in
  match ty with
  | Unit -> Ok ()
  | _ -> Err (`ExGot ("unit", ty))

let as_prod m =
  let* ty = m in
  match ty with
  | Prod (s, t) -> Ok (s, t)
  | _ -> Err (`ExGot ("product", ty))

let as_sum m =
  let* ty = m in
  match ty with
  | Sum (s, t) -> Ok (s, t)
  | _ -> Err (`ExGot ("sum", ty))

let as_arr m =
  let* ty = m in
  match ty with
  | Arr (s, t) -> Ok (s, t)
  | _ -> Err (`ExGot ("function", ty))

let as_neg m =
  let* ty = m in
  match ty with
  | Neg t -> Ok t
  | _ -> Err (`ExGot ("negation", ty))

let fresh =
  let x = ref (-1) in
  let fresh () =
    x := !x + 1;
    !x
  in fresh

(* Γ ⊢ e ⊣ Δ *)
let rec check (vars : var ctx) (e : exp) (covars : covar ctx) =
  match e with
  (* Axiom (context lookup)

    ——————————————————————————
    Γ, x : τ ⊢ [k]x ⊣ k : τ, Δ
 
       Γ ⊢ [k]x ⊣ Δ
    ——————————————————— x ≠ y
    Γ, y : τ ⊢ [k]x ⊣ Δ
 
       Γ ⊢ [k]x ⊣ Δ
    ——————————————————— j ≠ k
    Γ ⊢ [k]x ⊣ j : τ, Δ       *)
  | Axiom (k, x) ->
    let* t = find_var x vars in
    let* t' = find_covar k covars in
    if t = t' then Ok () else Err (`Mismatch (t, t'))
  (* Γ ⊢ e₁ ⊣ k : τ, Δ    Γ, x : τ ⊢ e₂ ⊣ Δ
     —————————————————————————————————————— Cut
         Γ ⊢ let x = κ k. e₁ in e₂ ⊣ Δ           *)
  | Let (x, t, k, e₁, e₂) ->
    check vars e₁ (add k t covars) *>
    check (add x t vars) e₂ covars
  (*
    ——————————————————    ——————————————
    x : 0 ⊢ absurd x ⊣    ⊢ [k]★ ⊣ k : 1 *)
  | Absurd x -> Ok ()
  | Trivial k -> as_unit (find_covar k covars)
  (*    Γ ⊢ e₁ ⊣ h : σ, Δ    Γ ⊢ e₂ ⊣ j : τ, Δ
     —————————————————————————————————————————————
     Γ ⊢ pair k (κ h. e₁) (κ j. e₂) ⊣ k : σ × τ, Δ *)
  | Pair (k, h, e₁, j, e₂) ->
    let* (s, t) = as_prod (find_covar k covars) in
    check vars e₁ (add h s covars) *>
    check vars e₂ (add j t covars)
  (*        Γ, y : σ, z : τ ⊢ e ⊣ Δ
     ——————————————————————————————————————
     Γ, x : σ × τ ⊢ let (y, z) = x in e ⊣ Δ *)
  | Unpair (y, z, x, e) ->
    let* (s, t) = as_prod (find_var x vars) in
    check (add y s (add z t vars)) e covars
  (*        Γ ⊢ e ⊣ h : σ, j : τ, Δ
     ——————————————————————————————————————
     Γ ⊢ let [h, j] = k in e ⊣ k : σ + τ, Δ *)
  | Uncase (h, j, k, e) ->
    let* (s, t) = as_sum (find_covar k covars) in
    check vars e (add h s (add j t covars))
  (*  Γ, y : σ ⊢ e₁ ⊣ Δ    Γ, z : τ ⊢ e₂ ⊣ Δ
     —————————————————————————————————————————
     Γ, x : σ + τ ⊢ case x (λ y. e₁) (λ z. e₂) *)
  | Case (x, y, e₁, z, e₂) ->
    let* (s, t) = as_sum (find_var x vars) in
    check (add y s vars) e₁ covars *>
    check (add z t vars) e₂ covars
  (*       Γ, x : σ ⊢ e ⊣ j : τ, Δ
     ———————————————————————————————————
     Γ ⊢ [k](λ x. κ j. e) ⊣ k : σ → τ, Δ *)
  | Fun (k, x, j, e) ->
    let* (s, t) = as_arr (find_covar k covars) in
    check (add x s vars) e (add j t covars)
  (*    Γ ⊢ e₁ ⊣ k : σ, Δ    Γ, y : τ ⊢ e₂ ⊣ Δ
     ————————————————————————————————————————————
     Γ, x : σ → τ ⊢ let y = x (κ k. e₁) in e₂ ⊣ Δ *)
  | LetApp (y, x, k, e₁, e₂) ->
    let* (s, t) = as_arr (find_var x vars) in
    check vars e₁ (add k s covars) *>
    check (add y t vars) e₂ covars
  (*         Γ ⊢ e ⊣ k : τ, Δ
     ————————————————————————————————
     Γ, x : ¬ τ ⊢ let x -> k in e ⊣ Δ *)
  | ToCo (x, k, e) ->
    let* t = as_neg (find_var x vars) in
    check vars e (add k t covars)
  (*         Γ, x : τ ⊢ e ⊣ Δ
     ————————————————————————————————
     Γ ⊢ let x <- k in e ⊣ k : ¬ τ, Δ *)
  | OfCo (x, k, e) ->
    let* t = as_neg (find_covar k covars) in
    check (add x t vars) e covars

(* Conversion to lambda calculus *)

type lc
  = LVar of int
  | Lam of (int -> lc)
  | App of lc * lc
  | LTrivial
  | LAbsurd of lc
  | In1 of lc
  | In2 of lc
  | LCase of lc * (int -> lc) * (int -> lc)
  | LPair of lc * lc
  | LUnpair of lc * (int -> int -> lc)

let ( $ ) e₁ e₂ = App (e₁, e₂)
let lam f = Lam (fun x -> f (LVar x))
let xlam f = Lam (fun x -> f (Var x))
let klam f = Lam (fun x -> f (Covar x))

let c_x (Var x) = LVar x
let c_k (Covar x) = LVar x

let rec c_exp : exp -> lc = function
  (* [[ [k]x ]] = k x *)
  | Axiom (k, x) -> c_k k $ c_x x
  (* [[ let x = κ k. e₁ in e₂ ]] = (λ k. [[e₁]]) (λ x. [[e₂]]) *)
  | Let (x, _, k, e₁, e₂) -> klam (fun k -> c_exp e₁) $ xlam (fun x -> c_exp e₂)
  (* [[ [k]★ ]] = k ★ *)
  | Trivial k -> c_k k $ LTrivial
  (* [[ absurd x ]] = case x of end *)
  | Absurd x -> LAbsurd (c_x x)
  (* [[ pair k (κ h. e₁) (κ j. e₂) ]] = (λ h. [[e₁]]) (λ v. (λ j. [[e₂]]) (λ w. k (v, w))) *)
  | Pair (k, h, e₁, j, e₂) ->
    klam (fun h -> c_exp e₁) $ lam (fun v -> 
    klam (fun j -> c_exp e₂) $ lam (fun w -> 
    LPair (v, w)))
  (* [[ let (y, z) = x in e ]] = let (y, z) = x in [[e]] *)
  | Unpair (y, z, x, e) -> LUnpair (c_x x, fun y z -> c_exp e)
  (* [[ let [h, j] = k in e ]] = (λ h j. [[e]]) (λ v. k (ι₁ v)) (λ w. k (ι₂ w)) *)
  | Uncase (h, j, k, e) ->
    (klam (fun h -> klam (fun j -> c_exp e))
      $ lam (fun v -> c_k k $ In1 v))
      $ lam (fun w -> c_k k $ In2 w)
  (* [[ case x (λ y. e₁) (λ z. e₂) ]] = case x of ι₁ y -> [[e₁]] | ι₂ z -> [[e₂]] end *)
  | Case (x, y, e₁, z, e₂) -> LCase (c_x x, (fun y -> c_exp e₁), fun z -> c_exp e₂)
  (* [[ [k](λ x. κ j. e) ]] = k (λ x j. [[e]]) *)
  | Fun (k, x, j, e) -> c_k k $ xlam (fun x -> klam (fun j -> c_exp e))
  (* [[ let y = x (κ k. e₁) in e₂ ]] = (λ k. e₁) (λ v. (λ y. e₂) (x v)) *)
  | LetApp (y, x, k, e₁, e₂) ->
    klam (fun k -> c_exp e₁) $ lam (fun v -> xlam (fun y -> c_exp e₂) $ (c_x x $ v))
  (* [[ let x -> k in e ]] = (λ k. [[e]]) x *)
  | ToCo (x, k, e) -> klam (fun k -> c_exp e) $ c_x x
  (* [[ let x <- k in e ]] = k (λ x. [[e]]) *)
  | OfCo (x, k, e) -> c_k k $ xlam (fun x -> c_exp e)

(* Pretty-printing for sequent calculus terms *)

let cat = String.concat ""

let p_x (Var x) = "x" ^ string_of_int x
let p_k (Covar k) = "k" ^ string_of_int k

let rec p_ty : ty -> string = function
  | Void -> "0"
  | Unit -> "1"
  | Sum (s, t) -> cat ["("; p_ty s; " + "; p_ty t; ")"]
  | Prod (s, t) -> cat ["("; p_ty s; " × "; p_ty t; ")"]
  | Arr (s, t) -> cat ["("; p_ty s; " → "; p_ty t; ")"]
  | Neg t -> cat ["¬"; p_ty t]
  | Vdash (ss, ts) ->
    cat ["("; String.concat ", " (List.map p_ty ss); " ⊢ "; String.concat ", " (List.map p_ty ts); ")"]

let rec p_exp : exp -> string = function
  | Axiom (k, x) -> cat ["["; p_k k; "]"; p_x x]
  | Let (x, t, k, e₁, e₂) ->
    cat ["let "; p_x x; " : "; p_ty t; " = "; p_kappa' k e₁; " in "; p_exp e₂]
  | Absurd x -> cat ["absurd "; p_x x]
  | Trivial k -> cat ["["; p_k k; "]★"]
  | Pair (k, h, e₁, j, e₂) -> cat ["pair "; p_k k; " "; p_kappa' h e₁; " "; p_kappa' j e₂]
  | Unpair (y, z, x, e) -> cat ["let ("; p_x y; ", "; p_x z; ") = "; p_x x; " in "; p_exp e]
  | Uncase (h, j, k, e) -> cat ["let ["; p_k h; ", "; p_k j; "] = "; p_k k; " in "; p_exp e]
  | Case (x, y, e₁, z, e₂) -> cat ["case "; p_x x; " "; p_lambda' y e₁; " "; p_lambda' z e₂]
  | Fun (k, x, j, e) -> cat ["["; p_k k; "](λ "; p_x x; ". κ "; p_k j; ". "; p_exp e]
  | LetApp (y, x, k, e₁, e₂) -> cat ["let "; p_x y; " = "; p_x x; " "; p_kappa' k e₁; " in "; p_exp e₂]
  | ToCo (x, k, e) -> cat ["let "; p_x x; " -> "; p_k k; " in "; p_exp e]
  | OfCo (x, k, e) -> cat ["let "; p_x x; " <- "; p_k k; " in "; p_exp e]
and p_kappa ke = let k = Covar (fresh ()) in cat ["(κ "; p_k k; ". "; p_exp (ke k)]
and p_kappa' k e = cat ["(κ "; p_k k; ". "; p_exp e]
and p_lambda xe = let x = Var (fresh ()) in cat ["(λ "; p_x x; ". "; p_exp (xe x)]
and p_lambda' x e = cat ["(λ "; p_x x; ". "; p_exp e]

(* Pretty-printing for lambda terms *)

let rec p_lx x = "x" ^ string_of_int x

let rec p_lc : lc -> string = function
  | LVar x -> p_lx x
  | Lam xe -> let x = fresh () in cat ["(λ "; p_lx x; ". "; p_lc (xe x); ")"]
  | App (e₁, e₂) -> cat ["("; p_lc e₁; " "; p_lc e₂; ")"]
  | LTrivial -> "★"
  | LAbsurd e -> cat ["case "; p_lc e; " of end"]
  | In1 e -> cat ["(ι₁ "; p_lc e; ")"]
  | In2 e -> cat ["(ι₂ "; p_lc e; ")"]
  | LCase (e, xe₁, ye₂) ->
    let x = fresh () in
    let y = fresh () in
    cat ["case "; p_lc e;
      " of ι₁ "; p_lx x; " -> "; p_lc (xe₁ x);
      " | ι₂ "; p_lx y; " -> "; p_lc (ye₂ y); " end"]
  | LPair (e₁, e₂) -> cat ["("; p_lc e₁; ", "; p_lc e₂; ")"]
  | LUnpair (e, xye) ->
    let x = fresh () in
    let y = fresh () in
    cat ["let ("; p_lx x; ", "; p_lx y; ") = "; p_lc e; " in "; p_lc (xye x y)]

(* Tests *)

let () = print_endline (p_lc (lam (fun x -> x $ x)))

let (dne_l, dne_lx, dne_lk) =
  let x = Var (fresh ()) in
  let j = Covar (fresh ()) in
  let y = Var (fresh ()) in
  let k = Covar (fresh ()) in
  (ToCo (x, j, OfCo (y, j, Axiom (k, y))), x, k)

let () = print_endline (p_exp dne_l)
let () = print_endline (p_lc (c_exp dne_l))

let dne_r =
  let x = Var (fresh ()) in
  let y = Var (fresh ()) in
  let k = Covar (fresh ()) in
  let j = Covar (fresh ()) in
  OfCo (y, k, ToCo (y, j, Axiom (j, x)))

let () = print_endline (p_exp dne_r)
let () = print_endline (p_lc (c_exp dne_r))

(* x : ¬ ¬ 1 ⊢ let x -> j in let y <- j in k[y] ⊣ k : 1 *)
let res = check (add dne_lx (Neg (Neg Unit)) empty) dne_l (add dne_lk Unit empty)

let res = check (add dne_lx (Neg (Neg Unit)) empty) (Axiom (dne_lk, dne_lx)) (add dne_lk Unit empty)
