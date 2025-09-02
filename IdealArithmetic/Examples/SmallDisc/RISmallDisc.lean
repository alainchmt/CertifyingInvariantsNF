
import IdealArithmetic.CertificateDedekind
import IdealArithmetic.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import IdealArithmetic.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.SmallDisc.IrreducibleSmallDisc


open Polynomial

noncomputable def T : ℤ[X] := X^5 + 20*X - 16
lemma T_def : T = X^5 + 20*X - 16 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  infer_instance

local notation "l" => [-16, 20, 0, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/4*a^4]

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  4
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![4, 0, 0, 0, 0], ![0, 4, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, -2, 0, 1, 0], ![0, 0, 0, 0, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
![![0, 1, 0, 0, 0],![0, 0, 2, 0, 0],![0, 1, 0, 2, 0],![0, 0, -1, 0, 1],![4, -5, 0, 0, 0]],
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![0, 0, 0, 0, 1],![2, -3, 0, -1, 0],![0, 2, -5, 0, 0]],
![![0, 0, 0, 1, 0],![0, 0, -1, 0, 1],![2, -3, 0, -1, 0],![0, 1, -2, 0, -1],![-2, 0, 2, -5, 0]],
![![0, 0, 0, 0, 1],![4, -5, 0, 0, 0],![0, 2, -5, 0, 0],![-2, 0, 2, -5, 0],![0, 2, 0, 4, -5]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-4]],![[], [], [], [-2], [0, -2]],![[], [], [-2], [0, -1], [2, 0, -1]],![[], [-4], [0, -2], [2, 0, -1], [0, 0, 0, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 2, 0, 0], [0, 1, 0, 2, 0], [0, 0, -1, 0, 1], [4, -5, 0, 0, 0]],
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 0, 0, 0, 1], [2, -3, 0, -1, 0], [0, 2, -5, 0, 0]],
 ![[0, 0, 0, 1, 0], [0, 0, -1, 0, 1], [2, -3, 0, -1, 0], [0, 1, -2, 0, -1], [-2, 0, 2, -5, 0]],
 ![[0, 0, 0, 0, 1], [4, -5, 0, 0, 0], [0, 2, -5, 0, 0], [-2, 0, 2, -5, 0], [0, 2, 0, 4, -5]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [4, -3, 1, 1, 1]
 g :=  [4, 1]
 h :=  [1, 1, 1, 1, 1]
 a :=  [4]
 b :=  [0, 3, 2, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 2
 p := ![2, 5]
 exp := ![16, 6]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp5.out
 a := [-12800000, -12800000, -12800000, -12800000]
 b := [40960000, 2560000, 2560000, 2560000, 2560000]
 hab := by decide
 hd := by
  intro p hp
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 3
 n := 2
 t :=  3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]],
![[0, 1, 0, 0, 0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 1], [0, 1, 0, 0, 0]],
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 1], [0, 1, 0, 1, 0], [0, 0, 1, 0, 0]],
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 1], [0, 1, 0, 1, 0], [0, 1, 0, 0, 1], [0, 0, 0, 1, 0]],
![[0, 0, 0, 0, 1], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 1],![0, 0, 0, 1, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0]]
 v := ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 1],![0, 0, 0, 1, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1]]
 v_ind := ![1, 2, 3]
 w_ind := ![0, 4]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide
 g := ![![0, 0, 0, 1, 1],![0, 0, 1, 1, 0],![1, 1, 0, 0, 0],![1, 1, 1, 0, 0],![0, 1, 1, 0, 1]]
 w1 := ![1, 1, 1]
 w2 := ![0, 1]
 a := ![![-3, 0, -10],![-6, 15, -12],![-6, -4, 7],![-4, -2, 8],![0, -16, 10]]
 c := ![![2, -6],![2, -12],![4, 4],![5, -2],![6, -3]]
 hmulw := by decide
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide


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

lemma B_int_repr {n : ℤ} : B.equivFun.symm ![n, 0, 0, 0, 0] = n := by
  suffices B.equivFun.symm ![n, 0, 0, 0, 0] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
  rw [← B_one_repr, ← LinearEquiv.map_smul]
  simp only [Basis.equivFun_symm_apply, zsmul_eq_mul, Matrix.smul_cons, smul_eq_mul, mul_one,
    mul_zero, Matrix.smul_empty]

instance : IsDomain O := by
  haveI hirr : Fact $ Irreducible (map (algebraMap ℤ ℚ) T) :=
  {out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible}
  letI hola : Field K := by
    unfold K
    exact AdjoinRoot.instField
  haveI : IsDomain K := by infer_instance
  refine Subalgebra.isDomain O
