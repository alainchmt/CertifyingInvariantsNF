import IdealArithmetic.Examples.NF4_0_76176_2.PrimesBelow4_0_76176_2F0
import IdealArithmetic.Examples.NF4_0_76176_2.PrimesBelow4_0_76176_2F1

noncomputable section
abbrev eC := ![1, 29, 41]

def hC : (i : Fin _) → PrimesBelowBoundCertificateInterval O (eC i.castSucc) (eC (i.castSucc + 1)) 42 := by
  rintro ⟨i,hi⟩
  interval_cases i
  exact PB42I0
  exact PB42I1

lemma hel : ∀ (i : Fin _), eC i.castSucc < eC (i.castSucc + 1) := by decide

def PB42 : PrimesBelowBoundCertificate O 42 := by
  refine primesBelowBoundCertificate_of_Interval O eC 41 rfl rfl hel hC

def 𝔭 := primesBelowBoundCertificate_of_Interval_fun_aux O eC 41 hC

def e := primesBelowBoundCertificate_of_Interval_r_aux O eC 41 hC

lemma cert_eq_𝔭 : PB42.β = Fin.addCasesIter e 𝔭 := by
  exact primesBelowBoundCertificate_of_Interval_β_eq_fun_aux O eC 41 rfl rfl hel hC
