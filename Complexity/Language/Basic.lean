/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/
import Mathlib.Data.List.Basic

/-!
# A typed scalar source language

Source values are ordinary natural numbers, booleans and unit. Variables refer
to lexical bindings in a typed context, not to machine registers. Administrative
normal form separates atoms from primitive operations: arithmetic and comparison
results are explicitly bound before use. A primitive is a syntax constructor,
not an arbitrary Lean function accepted as executable code.

A finite signature table types first-order calls. A program supplies an actual
statement body for each signature, including bodies that call themselves. No
termination, machine representation, heap or time bound is implicit in this
syntax. The current scalar fragment has immutable lexical bindings; a binding's
continuation is its scope, and a return can occur inside that continuation.
-/

namespace Complexity.Language

/-- The value types supported by the scalar core. -/
inductive Ty where
  | nat
  | bool
  | unit
  deriving DecidableEq, Repr

/-- Mathematical values, interpreted using existing Lean types. -/
abbrev Value : Ty → Type
  | .nat => Nat
  | .bool => Bool
  | .unit => Unit

/-- A typed lexical position. Repeated types in a context remain distinct bindings. -/
inductive Var : List Ty → Ty → Type where
  | here {Γ : List Ty} {τ : Ty} : Var (τ :: Γ) τ
  | there {Γ : List Ty} {τ σ : Ty} : Var Γ τ → Var (σ :: Γ) τ

/-- A value for each typed lexical variable, using an ordinary dependent function. -/
abbrev Env (Γ : List Ty) := (τ : Ty) → Var Γ τ → Value τ

namespace Env

/-- The unique environment with no variables. -/
def empty : Env [] := fun _ v => nomatch v

/-- Look up a lexical value, inferring its type from the variable. -/
def get {Γ : List Ty} {τ : Ty} (env : Env Γ) (v : Var Γ τ) : Value τ := env τ v

/-- Introduce one fresh lexical binding, retaining the outer bindings. -/
def cons {Γ : List Ty} {τ : Ty} (value : Value τ) (outer : Env Γ) : Env (τ :: Γ) :=
  fun _ v => match v with
    | .here => value
    | .there v => outer.get v

/-- Observe the innermost binding. -/
def head {Γ : List Ty} {τ : Ty} (env : Env (τ :: Γ)) : Value τ := env.get .here

/-- Leave the innermost lexical scope. -/
def tail {Γ : List Ty} {τ : Ty} (env : Env (τ :: Γ)) : Env Γ :=
  fun _ v => env.get (.there v)

@[simp] theorem get_tail {Γ : List Ty} {τ σ : Ty} (env : Env (τ :: Γ))
    (v : Var Γ σ) : (tail env).get v = env.get (.there v) := rfl

@[simp] theorem cons_here {Γ : List Ty} {τ : Ty} (value : Value τ) (env : Env Γ) :
    (cons value env).get .here = value := rfl

@[simp] theorem cons_there {Γ : List Ty} {τ σ : Ty} (value : Value τ) (env : Env Γ)
    (v : Var Γ σ) : (cons value env).get (.there v) = env.get v := rfl

@[simp] theorem head_cons {Γ : List Ty} {τ : Ty} (value : Value τ) (env : Env Γ) :
    head (cons value env) = value := rfl

@[simp] theorem tail_cons {Γ : List Ty} {τ : Ty} (value : Value τ) (env : Env Γ) :
    @Eq (Env Γ) (tail (cons value env)) env := rfl

@[simp] theorem cons_head_tail {Γ : List Ty} {τ : Ty} (env : Env (τ :: Γ)) :
    @Eq (Env (τ :: Γ)) (cons (head env) (tail env)) env := by
  funext σ v
  cases v <;> rfl

/-- A predicate on the empty source environment has no remaining arguments. -/
theorem forall_nil (p : Env [] → Prop) : (∀ env, p env) ↔ p empty := by
  constructor
  · intro h
    exact h empty
  · intro h env
    have same : env = empty := by
      funext τ v
      cases v
    exact same.symm ▸ h

/-- Quantifying over a source environment is ordinary quantification over its
head value and remaining arguments. No representation or register map is involved. -/
theorem forall_cons {Γ : List Ty} {τ : Ty} (p : Env (τ :: Γ) → Prop) :
    (∀ env, p env) ↔ ∀ value outer, p (cons value outer) := by
  constructor
  · intro h value outer
    exact h (cons value outer)
  · intro h env
    simpa only [cons_head_tail] using h (head env) (tail env)

end Env

/-- Atoms only observe an existing variable or materialize a literal value. -/
inductive Atom (Γ : List Ty) : Ty → Type where
  | var {τ : Ty} : Var Γ τ → Atom Γ τ
  | nat : Nat → Atom Γ .nat
  | bool : Bool → Atom Γ .bool
  | unit : Atom Γ .unit

/-- The independent mathematical meaning of an atom. -/
@[simp] def Atom.eval {Γ : List Ty} {τ : Ty} (atom : Atom Γ τ) (env : Env Γ) : Value τ :=
  match atom with
  | .var v => env.get v
  | .nat value => value
  | .bool value => value
  | .unit => ()

/-- Explicit scalar operations in administrative normal form. Natural arithmetic
has Lean's mathematical meaning: subtraction saturates at zero, division by zero
returns zero, and reduction modulo zero returns the dividend. -/
inductive Prim (Γ : List Ty) : Ty → Type where
  | atom {τ : Ty} : Atom Γ τ → Prim Γ τ
  | add : Atom Γ .nat → Atom Γ .nat → Prim Γ .nat
  | mul : Atom Γ .nat → Atom Γ .nat → Prim Γ .nat
  | sub : Atom Γ .nat → Atom Γ .nat → Prim Γ .nat
  | div : Atom Γ .nat → Atom Γ .nat → Prim Γ .nat
  | mod : Atom Γ .nat → Atom Γ .nat → Prim Γ .nat
  | eq : Atom Γ .nat → Atom Γ .nat → Prim Γ .bool
  | lt : Atom Γ .nat → Atom Γ .nat → Prim Γ .bool
  | le : Atom Γ .nat → Atom Γ .nat → Prim Γ .bool

/-- The mathematical meaning of the supported, explicitly enumerated primitives. -/
@[simp] def Prim.eval {Γ : List Ty} {τ : Ty} (prim : Prim Γ τ) (env : Env Γ) : Value τ :=
  match prim with
  | .atom a => a.eval env
  | .add left right => left.eval env + right.eval env
  | .mul left right => left.eval env * right.eval env
  | .sub left right => left.eval env - right.eval env
  | .div left right => left.eval env / right.eval env
  | .mod left right => left.eval env % right.eval env
  | .eq left right => decide (left.eval env = right.eval env)
  | .lt left right => decide (left.eval env < right.eval env)
  | .le left right => decide (left.eval env ≤ right.eval env)

/-- A first-order function's parameter types and result type. -/
structure Signature where
  params : List Ty
  result : Ty
  deriving DecidableEq, Repr

/-- Actual call operands, with exactly the types required by a signature. -/
inductive Args (Γ : List Ty) : List Ty → Type where
  | nil : Args Γ []
  | cons {τ : Ty} {params : List Ty} : Atom Γ τ → Args Γ params → Args Γ (τ :: params)

/-- Bind the actual atomic argument values in an independent callee environment. -/
@[simp] def Args.eval {Γ params : List Ty} (args : Args Γ params) (env : Env Γ) : Env params :=
  match args with
  | .nil => Env.empty
  | .cons value rest => Env.cons (value.eval env) (rest.eval env)

/-- Typed statements. A primitive or call result is scoped over its continuation;
sequencing and branches keep the enclosing context and declared return type. -/
inductive Stmt (signatures : List Signature) : List Ty → Ty → Type where
  | skip {Γ : List Ty} {result : Ty} : Stmt signatures Γ result
  | letPrim {Γ : List Ty} {τ result : Ty} (value : Prim Γ τ)
      (continuation : Stmt signatures (τ :: Γ) result) : Stmt signatures Γ result
  | call {Γ : List Ty} {result : Ty} (fn : Fin signatures.length)
      (args : Args Γ signatures[fn].params)
      (continuation : Stmt signatures (signatures[fn].result :: Γ) result) :
      Stmt signatures Γ result
  | seq {Γ : List Ty} {result : Ty} (first second : Stmt signatures Γ result) :
      Stmt signatures Γ result
  | ite {Γ : List Ty} {result : Ty} (condition : Atom Γ .bool)
      (yes no : Stmt signatures Γ result) : Stmt signatures Γ result
  | ret {Γ : List Ty} {result : Ty} (value : Atom Γ result) : Stmt signatures Γ result

/-- A finite function table whose entries are actual typed statement bodies.
The function field selects syntax; it is not an executable host callback. -/
structure Program (signatures : List Signature) where
  body : (fn : Fin signatures.length) →
    Stmt signatures signatures[fn].params signatures[fn].result

end Complexity.Language
