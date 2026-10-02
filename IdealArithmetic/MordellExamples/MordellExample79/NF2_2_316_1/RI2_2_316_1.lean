
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import IdealArithmetic.ConductorSubalgebraBuilder
import IdealArithmetic.PrimeIdealsKummer
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.MordellExamples.MordellExample79.NF2_2_316_1.Irreducible2_2_316_1
import IdealArithmetic.DedekindProject.Discriminant

namespace NF2_2_316_1



open Polynomial Module

noncomputable def T : ℤ[X] := X^2 - 79
lemma T_def : T = X^2 - 79 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-79, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, s] 

noncomputable def BQ : SubalgebraBuilderLists 2 ℤ  ℚ K T l where
 d := 1
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![1, 0], ![0, 1]]
 a := ![ ![![1, 0],![0, 1]], 
![![0, 1],![79, 0]]]
 s := ![![[], []],![[], [-1]]]
 h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide 

lemma T_degree : T.natDegree = 2 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B' : Basis (Fin 2) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 2) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ

noncomputable def B : Basis (Fin 2) ℤ O := timesTableO.basis
def Table : Fin 2 → Fin 2 → List ℤ := 
 ![ ![[1, 0], [0, 1]], 
 ![[0, 1], [79, 0]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp79: Fact $ Nat.Prime 79 := fact_iff.2 (by norm_num)

def CD2: CertificateDedekindCriterionLists l 2 where
 n := 2
 a' := []
 b' := [1]
 k := [1]
 f := [40, 1]
 g := [1, 1]
 h := [1, 1]
 a := [1]
 b := [1]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD79: CertificateDedekindCriterionLists l 79 where
 n := 2
 a' := []
 b' := [1]
 k := [1]
 f := [1]
 g := [0, 1]
 h := [0, 1]
 a := [1]
 b := []
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
 n := 2
 p := ![2, 79]
 exp := ![2, 1]
 pdgood := [2, 79]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp79.out
 a := [-4]
 b := [0, 2]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
  exact satisfiesDedekindCriterion_of_certificate_lists T l 79 T_ofList CD79


open BigOperators Classical Matrix Polynomial

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm ![1, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr

instance : IsDomain O := by
  haveI hirr : Fact $ Irreducible (map (algebraMap ℤ ℚ) T) :=
  {out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible}
  letI hola : Field K := by
    unfold K
    exact AdjoinRoot.instField
  haveI : IsDomain K := by infer_instance
  refine Subalgebra.isDomain O

 noncomputable instance : Mul (Ideal ↥O) := Submodule.mul (R := O) (A := O)
 noncomputable instance  : AddCommMonoid ↥O := AddSubmonoidClass.toAddCommMonoid O
 noncomputable instance : Module ℤ O := O.instModuleSubtypeMem
 noncomputable instance  : Algebra ℤ O := O.algebra'


lemma hroot_coord :
    timesTableO.basis.equivFun.symm ![0, 1] = ⟨θ, hroot_mem⟩ :=
  root_coord_subalgebraBuilder BQ ![0, 1] [] (by decide)

lemma minpoly_hroot :
    minpoly ℤ (timesTableO.basis.equivFun.symm ![0, 1]) = ofList l := by
  rw [hroot_coord]
  exact minpoly_root_subalgebra BQ hroot_mem

lemma conductor_hroot_coprime (p : ℕ) (gcd : Int.gcd BQ.d p = 1) :
    Ideal.comap (algebraMap ℤ O) (conductor ℤ (timesTableO.basis.equivFun.symm ![0, 1]))
      ⊔ Ideal.span {(p : ℤ)} = ⊤ := by
  rw [hroot_coord]
  exact conductor_coprime_of_coprime_int BQ hroot_mem p gcd

end NF2_2_316_1
