
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.Paper.NF5_1_157265_1.Irreducible5_1_157265_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 3*X^3 + 9*X - 8
lemma T_def : T = X^5 - 3*X^3 + 9*X - 8 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-8, 9, 0, -3, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a^2 - 1/2*a, 1/2*a^4 - 1/2*a]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d := 2
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, -1, -1, 1, 0], ![0, -1, 0, 0, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 1, 2, 0],![0, 0, -1, -1, 1],![4, -3, 1, 3, 0]],
![![0, 0, 1, 0, 0],![0, 1, 1, 2, 0],![0, 1, 0, 0, 2],![4, -4, 1, 2, -1],![0, 5, -5, -1, 3]],
![![0, 0, 0, 1, 0],![0, 0, -1, -1, 1],![4, -4, 1, 2, -1],![-4, 6, -3, -2, 1],![4, -8, 4, -1, -2]],
![![0, 0, 0, 0, 1],![4, -3, 1, 3, 0],![0, 5, -5, -1, 3],![4, -8, 4, -1, -2],![-4, 11, -6, 1, 0]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-2]],![[], [], [], [-2], [0, -2]],![[], [], [-2], [2, -1], [-2, 1, -1]],![[], [-2], [0, -2], [-2, 1, -1], [2, -3, 0, -1]]]
 h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ

noncomputable def B : Basis (Fin 5) ℤ O := timesTableO.basis
def Table : Fin 5 → Fin 5 → List ℤ :=
 ![ ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 2, 0], [0, 0, -1, -1, 1], [4, -3, 1, 3, 0]],
 ![[0, 0, 1, 0, 0], [0, 1, 1, 2, 0], [0, 1, 0, 0, 2], [4, -4, 1, 2, -1], [0, 5, -5, -1, 3]],
 ![[0, 0, 0, 1, 0], [0, 0, -1, -1, 1], [4, -4, 1, 2, -1], [-4, 6, -3, -2, 1], [4, -8, 4, -1, -2]],
 ![[0, 0, 0, 0, 1], [4, -3, 1, 3, 0], [0, 5, -5, -1, 3], [4, -8, 4, -1, -2], [-4, 11, -6, 1, 0]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp443: Fact $ Nat.Prime 443 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp71: Fact $ Nat.Prime 71 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n := 2
 a' := [2, 4]
 b' := [1, 1, 4]
 k := [2, 0, 3, 1]
 f := [2, -1, 1, 2, 1]
 g := [2, 2, 3, 4, 1]
 h := [1, 1]
 a := [0, 0, 0, 3]
 b := [3, 2, 1, 2]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD71: CertificateDedekindCriterionLists l 71 where
 n := 2
 a' := [15, 31, 62]
 b' := [26, 6, 45, 20]
 k := [52, 2, 14, 1]
 f := [56, 35, 42, 7, 1]
 g := [62, 38, 46, 7, 1]
 h := [64, 1]
 a := [6, 49, 53, 26]
 b := [53, 55, 18, 45]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD443: CertificateDedekindCriterionLists l 443 where
 n := 2
 a' := [167, 308, 410]
 b' := [277, 166, 172, 119]
 k := [361, 235, 322, 1]
 f := [226, 116, 143, 103, 1]
 g := [355, 181, 224, 161, 1]
 h := [282, 1]
 a := [79, 394, 64, 431]
 b := [369, 108, 126, 12]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 4
 p := ![2, 5, 71, 443]
 exp := ![4, 1, 1, 1]
 pdgood := [5, 71, 443]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp5.out
  exact hp71.out
  exact hp443.out
 a := [87392, -75312, -570240, -372360]
 b := [357264, -154336, -74304, 114048, 74472]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
  exact satisfiesDedekindCriterion_of_certificate_lists T l 71 T_ofList CD71
  exact satisfiesDedekindCriterion_of_certificate_lists T l 443 T_ofList CD443

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
 n := 5
 t := 3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 0], [0, 0, 1, 1, 1], [0, 1, 1, 1, 0]],
![[0, 0, 1, 0, 0], [0, 1, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 1], [0, 1, 1, 1, 1]],
![[0, 0, 0, 1, 0], [0, 0, 1, 1, 1], [0, 0, 1, 0, 1], [0, 0, 1, 0, 1], [0, 0, 0, 1, 0]],
![[0, 0, 0, 0, 1], [0, 1, 1, 1, 0], [0, 1, 1, 1, 1], [0, 0, 0, 1, 0], [0, 1, 0, 1, 0]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 1],![0, 1, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide

open BigOperators Classical Matrix Polynomial

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm ![1, 0, 0, 0, 0] = 1 := by
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

instance hirr : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

noncomputable section

instance K_field : Field K := by
  unfold K
  exact AdjoinRoot.instField

instance K_numberField : NumberField K := by
  unfold K
  exact AdjoinRoot.instNumberFieldRat

instance : Module ℚ K := Algebra.toModule
instance : @Algebra ℤ K CommRing.toCommSemiring CommRing.toCommSemiring.toSemiring :=
    Ring.toIntAlgebra K

lemma K_finrank : Module.finrank ℚ K = 5 := by
  unfold K
  erw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux _),
    Polynomial.natDegree_map_eq_of_injective, T_degree]
  · simp
  · exact RingHom.injective_int (algebraMap ℤ ℚ)
  · exact Irreducible.ne_zero hirr.out

theorem O_integral_closure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2]
  · fin_cases hc
    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K 2 _
      IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M2
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T _ T_ofList [2] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_integral_closure] ; rfl
