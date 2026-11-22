import PaperA.Assembly

noncomputable section
open EuclideanJordan
namespace PaperA

def coordSlot {K : Type} [Zero K] (conj : K → K) {n : ℕ}
    (i j : Fin n) (x : K) : Matrix (Fin n) (Fin n) K :=
  fun k l => if k = i ∧ l = j then x else if k = j ∧ l = i then conj x else 0
def coordDiag {K : Type} [Zero K] [One K] {n : ℕ} (i : Fin n) :
    Matrix (Fin n) (Fin n) K := fun k l => if k = i ∧ l = i then 1 else 0
def pauli (a : Spin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a.1+a.2 2 : ℝ), (a.2 0 : ℂ)-Complex.I*a.2 1;
     (a.2 0 : ℂ)+Complex.I*a.2 1, (a.1-a.2 2 : ℝ)]

variable {V : Type} [OrderUnitSpace V]
def orderEffect (a : V) : Prop := OrderUnitSpace.IsEffect a
abbrev orderUnit (V : Type) [OrderUnitSpace V] : V := OrderUnitSpace.ousUnit
structure OrderProduct (V : Type) [OrderUnitSpace V] where
  sp : V → V → V
  closed : ∀ a b, orderEffect a → orderEffect b → orderEffect (sp a b)
  S1 : ∀ a b c, orderEffect a → orderEffect b → orderEffect c → orderEffect (b+c) →
    sp a (b+c) = sp a b+sp a c
  S2 : ∀ b, orderEffect b → ContinuousOn (fun a => sp a b) {a | orderEffect a}
  S3 : ∀ a, orderEffect a → sp (orderUnit V) a = a
  S4 : ∀ a b, orderEffect a → orderEffect b → sp a b = 0 → sp b a = 0
  S5 : ∀ a b c, orderEffect a → orderEffect b → orderEffect c → sp a b = sp b a →
    sp a (sp b c) = sp (sp a b) c
  S6_compl : ∀ a b, orderEffect a → orderEffect b → sp a b = sp b a →
    sp a (orderUnit V-b) = sp (orderUnit V-b) a
  S6_sum : ∀ a b c, orderEffect a → orderEffect b → orderEffect c → orderEffect (b+c) →
    sp a b = sp b a → sp a c = sp c a → sp a (b+c) = sp (b+c) a
  S7 : ∀ a b c, orderEffect a → orderEffect b → orderEffect c →
    sp a b = sp b a → sp a c = sp c a → sp a (sp b c) = sp (sp b c) a

end PaperA
