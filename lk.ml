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
     | let x = κ k. e₁ in e₂ *)
  = Axiom of covar * var
  | Let of ty * (covar -> exp) * (var -> exp)
  (* Unit and zero
     | absurd x
     | [k]★ *)
  | Absurd of var
  | Trivial of covar
  (* Products
     | pair k (κ h. e₁) (κ j. e₂)
     | let (y, z) = x in e *)
  | Pair of covar * (covar -> exp) * (covar -> exp)
  | Unpair of var * (var -> var -> exp)
  (* Sums
     | let [h, j] = k in e
     | case x (λ y. e₁) (λ z. e₂) *)
  | Uncase of covar * (covar -> covar -> exp)
  | Case of var * (var -> exp) * (var -> exp)
  (* Functions
     | [k](λ x. κ j. e)
     | let y = x (κ k. e₁) in e₂ *)
  | Fun of covar * (var -> covar -> exp)
  | LetApp of var * (covar -> exp) * (var -> exp)
  (* Negation
     | let x -> k in e
     | let x <- k in e *)
  | ToCo of var * (covar -> exp)
  | OfCo of covar * (var -> exp)

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
  fun () ->
    x := !x + 1;
    !x

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
  | Let (t, ke1, xe2) ->
    let k = Covar (fresh ()) in
    let x = Var (fresh ()) in
    check vars (ke1 k) (add k t covars) *>
    check (add x t vars) (xe2 x) covars
  (*
    ——————————————————    ——————————————
    x : 0 ⊢ absurd x ⊣    ⊢ [k]★ ⊣ k : 1 *)
  | Absurd x -> Ok ()
  | Trivial k -> as_unit (find_covar k covars)
  (*    Γ ⊢ e₁ ⊣ h : σ, Δ    Γ ⊢ e₂ ⊣ j : τ, Δ
     —————————————————————————————————————————————
     Γ ⊢ pair k (κ h. e₁) (κ j. e₂) ⊣ k : σ × τ, Δ *)
  | Pair (k, he1, je2) ->
    let* (s, t) = as_prod (find_covar k covars) in
    let h = Covar (fresh ()) in
    let j = Covar (fresh ()) in
    check vars (he1 h) (add h s covars) *>
    check vars (je2 j) (add j t covars)
  (*        Γ, y : σ, z : τ ⊢ e ⊣ Δ
     ——————————————————————————————————————
     Γ, x : σ × τ ⊢ let (y, z) = x in e ⊣ Δ *)
  | Unpair (x, yze) ->
    let* (s, t) = as_prod (find_var x vars) in
    let y = Var (fresh ()) in
    let z = Var (fresh ()) in
    check (add y s (add z t vars)) (yze y z) covars
  (*        Γ ⊢ e ⊣ h : σ, j : τ, Δ
     ——————————————————————————————————————
     Γ ⊢ let [h, j] = k in e ⊣ k : σ + τ, Δ *)
  | Uncase (k, hje) ->
    let* (s, t) = as_sum (find_covar k covars) in
    let h = Covar (fresh ()) in
    let j = Covar (fresh ()) in
    check vars (hje h j) (add h s (add j t covars))
  (*  Γ, y : σ ⊢ e₁ ⊣ Δ    Γ, z : τ ⊢ e₂ ⊣ Δ
     —————————————————————————————————————————
     Γ, x : σ + τ ⊢ case x (λ y. e₁) (λ z. e₂) *)
  | Case (x, ye1, ze2) ->
    let* (s, t) = as_sum (find_var x vars) in
    let y = Var (fresh ()) in
    let z = Var (fresh ()) in
    check (add y s vars) (ye1 y) covars *>
    check (add z t vars) (ze2 z) covars
  (*       Γ, x : σ ⊢ e ⊣ j : τ, Δ
     ———————————————————————————————————
     Γ ⊢ [k](λ x. κ j. e) ⊣ k : σ → τ, Δ *)
  | Fun (k, xje) ->
    let* (s, t) = as_arr (find_covar k covars) in
    let x = Var (fresh ()) in
    let j = Covar (fresh ()) in
    check (add x s vars) (xje x j) (add j t covars)
  (*    Γ ⊢ e₁ ⊣ k : σ, Δ    Γ, y : τ ⊢ e₂ ⊣ Δ
     ————————————————————————————————————————————
     Γ, x : σ → τ ⊢ let y = x (κ k. e₁) in e₂ ⊣ Δ *)
  | LetApp (x, ke1, ye2) ->
    let* (s, t) = as_arr (find_var x vars) in
    let k = Covar (fresh ()) in
    let y = Var (fresh ()) in
    check vars (ke1 k) (add k s covars) *>
    check (add y t vars) (ye2 y) covars
  (*         Γ ⊢ e ⊣ k : τ, Δ
     ————————————————————————————————
     Γ, x : ¬ τ ⊢ let x -> k in e ⊣ Δ *)
  | ToCo (x, ke) ->
    let* t = as_neg (find_var x vars) in
    let k = Covar (fresh ()) in
    check vars (ke k) (add k t covars)
  (*         Γ, x : τ ⊢ e ⊣ Δ
     ————————————————————————————————
     Γ ⊢ let x <- k in e ⊣ k : ¬ τ, Δ *)
  | OfCo (k, xe) ->
    let* t = as_neg (find_covar k covars) in
    let x = Var (fresh ()) in
    check (add x t vars) (xe x) covars

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

let ( $ ) e1 e2 = App (e1, e2)
let lam f = Lam (fun x -> f (LVar x))
let xlam f = Lam (fun x -> f (Var x))
let klam f = Lam (fun x -> f (Covar x))

let c_x (Var x) = LVar x
let c_k (Covar x) = LVar x

let rec c_exp : exp -> lc = function
  (* [[ [k]x ]] = k x *)
  | Axiom (k, x) -> c_k k $ c_x x
  (* [[ let x = κ k. e₁ in e₂ ]] = (λ k. [[e₁]]) (λ x. [[e₂]]) *)
  | Let (_, ke1, xe2) -> klam (fun k -> c_exp (ke1 k)) $ xlam (fun x -> c_exp (xe2 x))
  (* [[ [k]★ ]] = k ★ *)
  | Trivial k -> c_k k $ LTrivial
  (* [[ absurd x ]] = case x of end *)
  | Absurd x -> LAbsurd (c_x x)
  (* [[ pair k (κ h. e₁) (κ j. e₂) ]] = (λ h. [[e₁]]) (λ v. (λ j. [[e₂]]) (λ w. k (v, w))) *)
  | Pair (k, he1, je2) ->
    klam (fun h -> c_exp (he1 h)) $ lam (fun v -> 
    klam (fun j -> c_exp (je2 j)) $ lam (fun w -> 
    LPair (v, w)))
  (* [[ let (y, z) = x in e ]] = let (y, z) = x in [[e]] *)
  | Unpair (x, yze) -> LUnpair (c_x x, fun y z -> c_exp (yze (Var y) (Var z)))
  (* [[ let [h, j] = k in e ]] = (λ h j. [[e]]) (λ v. k (ι₁ v)) (λ w. k (ι₂ w)) *)
  | Uncase (k, hje) ->
    (klam (fun h -> klam (fun j -> c_exp (hje h j)))
      $ lam (fun v -> c_k k $ In1 v))
      $ lam (fun w -> c_k k $ In2 w)
  (* [[ case x (λ y. e₁) (λ z. e₂) ]] = case x of ι₁ y -> [[e₁]] | ι₂ z -> [[e₂]] end *)
  | Case (x, ye1, ze2) -> LCase (c_x x, (fun y -> c_exp (ye1 (Var y))), fun z -> c_exp (ze2 (Var z)))
  (* [[ [k](λ x. κ j. e) ]] = k (λ x j. [[e]]) *)
  | Fun (k, xje) -> c_k k $ xlam (fun x -> klam (fun j -> c_exp (xje x j)))
  (* [[ let y = x (κ k. e₁) in e₂ ]] = (λ k. e₁) (λ v. (λ y. e₂) (x v)) *)
  | LetApp (x, ke1, ye2) ->
    klam (fun k -> c_exp (ke1 k)) $ lam (fun v -> xlam (fun y -> c_exp (ye2 y)) $ (c_x x $ v))
  (* [[ let x -> k in e ]] = (λ k. [[e]]) x *)
  | ToCo (x, ke) -> klam (fun k -> c_exp (ke k)) $ c_x x
  (* [[ let x <- k in e ]] = k (λ x. [[e]]) *)
  | OfCo (k, xe) -> c_k k $ xlam (fun x -> c_exp (xe x))

