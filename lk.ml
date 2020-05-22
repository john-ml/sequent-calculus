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
let extend (x : 'a) (t : ty) (c : 'a ctx) : 'a ctx =
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
  | LK of covar * var list * covar list * exp
  | LKApp of var * (covar * exp) list * (var * exp) list

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
  | _ -> Err (`ExGot ("1", ty))

let as_prod m =
  let* ty = m in
  match ty with
  | Prod (s, t) -> Ok (s, t)
  | _ -> Err (`ExGot ("_ × _", ty))

let as_sum m =
  let* ty = m in
  match ty with
  | Sum (s, t) -> Ok (s, t)
  | _ -> Err (`ExGot ("_ + _", ty))

let as_arr m =
  let* ty = m in
  match ty with
  | Arr (s, t) -> Ok (s, t)
  | _ -> Err (`ExGot ("_ → _", ty))

let as_neg m =
  let* ty = m in
  match ty with
  | Neg t -> Ok t
  | _ -> Err (`ExGot ("¬ _", ty))

let as_vdash m =
  let* ty = m in
  match ty with
  | Vdash (ss, ts) -> Ok (ss, ts)
  | _ -> Err (`ExGot ("_ ⊢ _", ty))

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
  | Let (x, t, k, e1, e2) ->
    check vars e1 (extend k t covars) *>
    check (extend x t vars) e2 covars
  (*
    ——————————————————    ——————————————
    x : 0 ⊢ absurd x ⊣    ⊢ [k]★ ⊣ k : 1 *)
  | Absurd x -> Ok ()
  | Trivial k -> as_unit (find_covar k covars)
  (*    Γ ⊢ e₁ ⊣ h : σ, Δ    Γ ⊢ e₂ ⊣ j : τ, Δ
     —————————————————————————————————————————————
     Γ ⊢ pair k (κ h. e₁) (κ j. e₂) ⊣ k : σ × τ, Δ *)
  | Pair (k, h, e1, j, e2) ->
    let* (s, t) = as_prod (find_covar k covars) in
    check vars e1 (extend h s covars) *>
    check vars e2 (extend j t covars)
  (*        Γ, y : σ, z : τ ⊢ e ⊣ Δ
     ——————————————————————————————————————
     Γ, x : σ × τ ⊢ let (y, z) = x in e ⊣ Δ *)
  | Unpair (y, z, x, e) ->
    let* (s, t) = as_prod (find_var x vars) in
    check (extend y s (extend z t vars)) e covars
  (*        Γ ⊢ e ⊣ h : σ, j : τ, Δ
     ——————————————————————————————————————
     Γ ⊢ let [h, j] = k in e ⊣ k : σ + τ, Δ *)
  | Uncase (h, j, k, e) ->
    let* (s, t) = as_sum (find_covar k covars) in
    check vars e (extend h s (extend j t covars))
  (*  Γ, y : σ ⊢ e₁ ⊣ Δ    Γ, z : τ ⊢ e₂ ⊣ Δ
     —————————————————————————————————————————
     Γ, x : σ + τ ⊢ case x (λ y. e₁) (λ z. e₂) *)
  | Case (x, y, e1, z, e2) ->
    let* (s, t) = as_sum (find_var x vars) in
    check (extend y s vars) e1 covars *>
    check (extend z t vars) e2 covars
  (*       Γ, x : σ ⊢ e ⊣ j : τ, Δ
     ———————————————————————————————————
     Γ ⊢ [k](λ x. κ j. e) ⊣ k : σ → τ, Δ *)
  | Fun (k, x, j, e) ->
    let* (s, t) = as_arr (find_covar k covars) in
    check (extend x s vars) e (extend j t covars)
  (*    Γ ⊢ e₁ ⊣ k : σ, Δ    Γ, y : τ ⊢ e₂ ⊣ Δ
     ————————————————————————————————————————————
     Γ, x : σ → τ ⊢ let y = x (κ k. e₁) in e₂ ⊣ Δ *)
  | LetApp (y, x, k, e1, e2) ->
    let* (s, t) = as_arr (find_var x vars) in
    check vars e1 (extend k s covars) *>
    check (extend y t vars) e2 covars
  (*         Γ ⊢ e ⊣ k : τ, Δ
     ————————————————————————————————
     Γ, x : ¬ τ ⊢ let x -> k in e ⊣ Δ *)
  | ToCo (x, k, e) ->
    let* t = as_neg (find_var x vars) in
    check vars e (extend k t covars)
  (*         Γ, x : τ ⊢ e ⊣ Δ
     ————————————————————————————————
     Γ ⊢ let x <- k in e ⊣ k : ¬ τ, Δ *)
  | OfCo (x, k, e) ->
    let* t = as_neg (find_covar k covars) in
    check (extend x t vars) e covars
  (*            Γ, x : σ, .. ⊢ e ⊣ j : τ, .., Δ
     —————————————————————————————————————————————————————
     Γ ⊢ [k](λ x .. . κ j .. . e) ⊣ k : (σ, .. ⊢ τ, ..), Δ *)
  | LK (k, xs, js, e) ->
    let* (ss, ts) = as_vdash (find_covar k covars) in
    let open List in
    if length xs = length ss then Err (`LKArgArity (xs, ss)) else
    if length js = length ts then Err (`LKContArity (js, ts)) else
    let extends vs ts vts = fold_right (fun (v, t) vts -> extend v t vts) (combine vs ts) vts in
    check (extends xs ss vars) e (extends js ts covars)
  (*          Γ ⊢ e₁ ⊣ k : σ, Δ    ..    Γ, y : τ ⊢ e₂ ⊣ Δ    ..
     ————————————————————————————————————————————————————————————————————
     Γ, x : (σ, .. ⊢ τ, ..) ⊢ case x (κ k. e₁) .. of (λ y. e₂) .. end ⊣ Δ *)
  | LKApp (x, kes, yes) ->
    let* (ss, ts) = as_vdash (find_var x vars) in
    let open List in
    if length kes = length ss then Err (`LKAppArgArity (kes, ss)) else
    if length yes = length ts then Err (`LKAppContArity (yes, ts)) else
    let mapM_ f xs = fold_left (fun m x -> m *> f x) (Ok ()) xs in
    mapM_ (fun ((k, e), s) -> check vars e (extend k s covars)) (combine kes ss) *>
    mapM_ (fun ((y, e), t) -> check (extend y t vars) e covars) (combine yes ts)

(* Conversion to lambda calculus *)

type lc
  = LVar of string
  | Lam of string * lc
  | App of lc * lc
  | LTrivial
  | LAbsurd of lc
  | In1 of lc
  | In2 of lc
  | LCase of lc * string * lc * string * lc
  | LPair of lc * lc
  | LUnpair of string * string * lc * lc

let s_x (Var x) = "x" ^ string_of_int x
let s_k (Covar k) = "k" ^ string_of_int k
let c_x x = LVar (s_x x)
let c_k k = LVar (s_k k)

let ( $ ) e1 e2 = App (e1, e2)
let vlam ve = let v = "v" ^ string_of_int (fresh ()) in Lam (v, ve (LVar v))
let xlam (Var x) e = Lam ("x" ^ string_of_int x, e)
let klam (Covar k) e = Lam ("k" ^ string_of_int k, e)

let rec c_exp : exp -> lc = function
  (* [[ [k]x ]] = k x *)
  | Axiom (k, x) -> c_k k $ c_x x
  (* [[ let x = κ k. e₁ in e₂ ]] = (λ k. [[e₁]]) (λ x. [[e₂]]) *)
  | Let (x, _, k, e1, e2) -> klam k (c_exp e1) $ xlam x (c_exp e2)
  (* [[ [k]★ ]] = k ★ *)
  | Trivial k -> c_k k $ LTrivial
  (* [[ absurd x ]] = case x of end *)
  | Absurd x -> LAbsurd (c_x x)
  (* [[ pair k (κ h. e₁) (κ j. e₂) ]] = (λ h. [[e₁]]) (λ v. (λ j. [[e₂]]) (λ w. k (v, w))) *)
  | Pair (k, h, e1, j, e2) ->
    klam h (c_exp e1) $ vlam (fun v -> 
    klam j (c_exp e2) $ vlam (fun w -> 
    LPair (v, w)))
  (* [[ let (y, z) = x in e ]] = let (y, z) = x in [[e]] *)
  | Unpair (y, z, x, e) -> LUnpair (s_x y, s_x z, c_x x, c_exp e)
  (* [[ let [h, j] = k in e ]] = (λ h j. [[e]]) (λ v. k (ι₁ v)) (λ w. k (ι₂ w)) *)
  | Uncase (h, j, k, e) ->
    (klam h (klam j (c_exp e))
      $ vlam (fun v -> c_k k $ In1 v))
      $ vlam (fun w -> c_k k $ In2 w)
  (* [[ case x (λ y. e₁) (λ z. e₂) ]] = case x of ι₁ y -> [[e₁]] | ι₂ z -> [[e₂]] end *)
  | Case (x, y, e1, z, e2) -> LCase (c_x x, s_x y, c_exp e1, s_x z, c_exp e2)
  (* [[ [k](λ x. κ j. e) ]] = k (λ x j. [[e]]) *)
  | Fun (k, x, j, e) -> c_k k $ xlam x (klam j (c_exp e))
  (* [[ let y = x (κ k. e₁) in e₂ ]] = (λ k. e₁) (λ v. (λ y. e₂) (x v)) *)
  | LetApp (y, x, k, e1, e2) ->
    klam k (c_exp e1) $ vlam (fun v -> xlam y (c_exp e2) $ (c_x x $ v))
  (* [[ let x -> k in e ]] = (λ k. [[e]]) x *)
  | ToCo (x, k, e) -> klam k (c_exp e) $ c_x x
  (* [[ let x <- k in e ]] = k (λ x. [[e]]) *)
  | OfCo (x, k, e) -> c_k k $ xlam x (c_exp e)
  (* [[ [k](λ x .. . κ j .. . e) ]] = k (λ x .. j .. . [[e]]) *)
  | LK (k, xs, js, e) -> let open List in c_k k $ fold_right xlam xs (fold_right klam js (c_exp e))
  (* [[ case x (κ k. e₁) .. of (λ y. e₂) .. end ]] = x (λ k. [[e₁]]) .. (λ y. [[e₂]]) .. *)
  | LKApp (x, kes, yes) ->
    let open List in
    fold_left (fun e (y, e2) -> e $ xlam y (c_exp e2))
      (fold_left (fun e (k, e1) -> e $ klam k (c_exp e1)) (c_x x) kes)
      yes

(* Pretty-printing for sequent calculus terms *)

let cat = String.concat ""
let unwords_by f xs = String.concat " " (List.map f xs)
let commas_by f xs = String.concat ", " (List.map f xs)

let p_x (Var x) = "x" ^ string_of_int x
let p_k (Covar k) = "k" ^ string_of_int k

let rec p_ty : ty -> string = function
  | Void -> "0"
  | Unit -> "1"
  | Sum (s, t) -> cat ["("; p_ty s; " + "; p_ty t; ")"]
  | Prod (s, t) -> cat ["("; p_ty s; " × "; p_ty t; ")"]
  | Arr (s, t) -> cat ["("; p_ty s; " → "; p_ty t; ")"]
  | Neg t -> cat ["¬"; p_ty t]
  | Vdash (ss, ts) -> cat ["("; commas_by p_ty ss; " ⊢ "; commas_by p_ty ts; ")"]

let rec p_exp : exp -> string = function
  | Axiom (k, x) -> cat ["["; p_k k; "]"; p_x x]
  | Let (x, t, k, e1, e2) ->
    cat ["let "; p_x x; " : "; p_ty t; " = "; p_kappa k e1; " in "; p_exp e2]
  | Absurd x -> cat ["absurd "; p_x x]
  | Trivial k -> cat ["["; p_k k; "]★"]
  | Pair (k, h, e1, j, e2) -> cat ["pair "; p_k k; " "; p_kappa h e1; " "; p_kappa j e2]
  | Unpair (y, z, x, e) -> cat ["let ("; p_x y; ", "; p_x z; ") = "; p_x x; " in "; p_exp e]
  | Uncase (h, j, k, e) -> cat ["let ["; p_k h; ", "; p_k j; "] = "; p_k k; " in "; p_exp e]
  | Case (x, y, e1, z, e2) -> cat ["case "; p_x x; " "; p_lambda y e1; " "; p_lambda z e2]
  | Fun (k, x, j, e) -> cat ["["; p_k k; "](λ "; p_x x; ". κ "; p_k j; ". "; p_exp e]
  | LetApp (y, x, k, e1, e2) -> cat ["let "; p_x y; " = "; p_x x; " "; p_kappa k e1; " in "; p_exp e2]
  | ToCo (x, k, e) -> cat ["let "; p_x x; " -> "; p_k k; " in "; p_exp e]
  | OfCo (x, k, e) -> cat ["let "; p_x x; " <- "; p_k k; " in "; p_exp e]
  | LK (k, xs, js, e) ->
    cat ["["; p_k k; "](λ "; unwords_by p_x xs; ". κ "; unwords_by p_k js; ". "; p_exp e]
  | LKApp (x, kes, yes) ->
    cat ["case "; p_x x; " "; unwords_by (fun (k, e) -> p_kappa k e) kes; " of ";
      unwords_by (fun (y, e) -> p_lambda y e) yes; " end"]
and p_kappa k e = cat ["(κ "; p_k k; ". "; p_exp e]
and p_lambda x e = cat ["(λ "; p_x x; ". "; p_exp e]

(* Pretty-printing for lambda terms *)

let rec p_lx x = "x" ^ string_of_int x
let rec p_lc : lc -> string = function
  | LVar x -> x
  | Lam (x, e) -> cat ["(λ "; x; ". "; p_lc e; ")"]
  | App (e1, e2) -> cat ["("; p_lc e1; " "; p_lc e2; ")"]
  | LTrivial -> "★"
  | LAbsurd e -> cat ["case "; p_lc e; " of end"]
  | In1 e -> cat ["(ι₁ "; p_lc e; ")"]
  | In2 e -> cat ["(ι₂ "; p_lc e; ")"]
  | LCase (e, x, e1, y, e2) ->
    cat ["case "; p_lc e;
      " of ι₁ "; x; " -> "; p_lc e1;
      " | ι₂ "; y; " -> "; p_lc e2; " end"]
  | LPair (e1, e2) -> cat ["("; p_lc e1; ", "; p_lc e2; ")"]
  | LUnpair (x, y, e1, e2) -> cat ["let ("; x; ", "; y; ") = "; p_lc e1; " in "; p_lc e2]

(* Tests *)

let () = print_endline (p_lc (vlam (fun x -> x $ x)))

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
let res = check (extend dne_lx (Neg (Neg Unit)) empty) dne_l (extend dne_lk Unit empty)

let res = check (extend dne_lx (Neg (Neg Unit)) empty) (Axiom (dne_lk, dne_lx)) (extend dne_lk Unit empty)
